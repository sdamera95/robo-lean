import RoboLean.Cell.Loop
import RoboLean.Cell.SupervisorRefines

/-!
# The executable cell supervisor in the sampled loop

This file runs the executable cell supervisor of `RoboLean.Cell.Supervisor` inside the sampled
loop of `RoboLean.Cell.Loop` and shows that every such timed run is a timed run of the loop.
A design model, not from MLS.

A loop state of the cell (`CellState`) is a state of the executable supervisor together with the
controller's record of the last admitted move (start, goal, admission boundary). At each boundary
the harness sends the supervisor a list of actions (`Boundary`): first any number of `request` and
`reject` actions (forwarding the planner's requests and rejecting the unlinked ones), then the
policy's one action (`PolicyStep`): while busy, `finish` when the move is due and arrived,
`timeout` when not and the age is at the bound, `tick` otherwise; while idle, nothing or `admit w`.
Every action must be accepted by the executable `step`. A timed run (`IsCellRun`) starts at
`State.init p.home` with the rest move at home.

Main results: the executable supervisor's state at every boundary is the result of `run` on all
the actions sent so far (`IsCellRun.run_eq`), so every invariant proved for the executable and the
design supervisor applies to it; while busy the supervisor's commanded list is the controller's
goal (`IsCellRun.commanded_eq`); and forgetting the requests, rejections and timed-out lists maps
the run to a timed run of the loop (`IsCellRun.isRun`), for loop data whose guard contains the
supervisor's link relation `CellLinked p.cells` and whose bound is the supervisor's.
-/

namespace RoboLean.Cell.Loop

open Set Supervisor

/-- The queue actions of a boundary: `request` and `reject`, which change only the supervisor's
request and rejection lists. A design model, not from MLS. -/
def IsQueueAction : Action → Prop
  | .request _ => True
  | .reject _ => True
  | _ => False

/-- A loop state of the cell: the executable supervisor's state and the controller's record of
the last admitted move, from `src` to `goal` admitted at boundary `start` (waypoints in rational
degrees). A design model, not from MLS. -/
structure CellState where
  /-- The executable supervisor's state. -/
  sup : Supervisor.State
  /-- The start waypoint of the last admitted move. -/
  src : Waypoint
  /-- The goal waypoint of the last admitted move. -/
  goal : Waypoint
  /-- The boundary index at which the last move was admitted. -/
  start : ℕ

/-- The initial loop state of the cell: the supervisor's initial state at `home` and the rest
move from `home` to `home` admitted at boundary `0`. A design model, not from MLS. -/
def CellState.init (home : Waypoint) : CellState :=
  ⟨Supervisor.State.init home, home, home, 0⟩

/-- The loop state of a cell state: the supervisor's `current`, `busy`, `faulted` and `age`, and
the controller's record. A design model, not from MLS. -/
def CellState.toLoop (c : CellState) : Loop.State Waypoint :=
  ⟨c.sup.current, c.sup.busy, c.sup.faulted, c.sup.age, c.src, c.goal, c.start⟩

/-- The policy's action at boundary `k` from the sample `(θ, θ')`, sent to the executable
supervisor with parameters `p` after the queue actions: `finish`, `timeout` or `tick` while busy
as in `Loop.Step`, nothing or `admit w` while idle; each action is accepted by `step`, and an
admission records the move from the current waypoint to `w` admitted at `k`. A design model, not
from MLS. -/
inductive PolicyStep (L : Loop.Params 3 Waypoint) (p : Supervisor.Params) (k : ℕ)
    (θ θ' : Fin 3 → ℝ) : CellState → List Action → CellState → Prop
  /-- Busy, due and arrived: `finish`. -/
  | finish (c : CellState) (s' : Supervisor.State) (hbusy : c.sup.busy = true)
      (hdue : Due L c.toLoop k) (harr : Arrived L c.goal θ θ')
      (hstep : step p c.sup .finish = some s') :
      PolicyStep L p k θ θ' c [.finish] { c with sup := s' }
  /-- Busy, not finished, age at the bound: `timeout`. -/
  | timeout (c : CellState) (s' : Supervisor.State) (hbusy : c.sup.busy = true)
      (hnot : ¬ (Due L c.toLoop k ∧ Arrived L c.goal θ θ')) (hage : c.sup.age = p.bound)
      (hstep : step p c.sup .timeout = some s') :
      PolicyStep L p k θ θ' c [.timeout] { c with sup := s' }
  /-- Busy, not finished, age not at the bound: `tick`. -/
  | tick (c : CellState) (s' : Supervisor.State) (hbusy : c.sup.busy = true)
      (hnot : ¬ (Due L c.toLoop k ∧ Arrived L c.goal θ θ')) (hage : c.sup.age ≠ p.bound)
      (hstep : step p c.sup .tick = some s') :
      PolicyStep L p k θ θ' c [.tick] { c with sup := s' }
  /-- Idle: no action. -/
  | wait (c : CellState) (hidle : c.sup.busy = false) : PolicyStep L p k θ θ' c [] c
  /-- Idle: `admit w`, accepted by the supervisor (so `w` is requested, the supervisor is not
  faulted and `w` is linked to the current waypoint). -/
  | admit (c : CellState) (w : Waypoint) (s' : Supervisor.State) (hidle : c.sup.busy = false)
      (hstep : step p c.sup (.admit w) = some s') :
      PolicyStep L p k θ θ' c [.admit w] ⟨s', c.sup.current, w, k⟩

/-- One boundary `k` of the cell loop with the sample `(θ, θ')`: the actions `acts` sent to the
supervisor are queue actions `pre`, accepted by `run`, followed by the policy's action `pol`. A
design model, not from MLS. -/
def Boundary (L : Loop.Params 3 Waypoint) (p : Supervisor.Params) (k : ℕ) (θ θ' : Fin 3 → ℝ)
    (c : CellState) (acts : List Action) (c' : CellState) : Prop :=
  ∃ pre pol : List Action, ∃ s₁ : Supervisor.State, acts = pre ++ pol ∧
    (∀ a ∈ pre, IsQueueAction a) ∧ run p c.sup pre = some s₁ ∧
    PolicyStep L p k θ θ' { c with sup := s₁ } pol c'

/-- A timed run of the cell loop for the motion `(x, v)`: the loop states `c k` before the
boundary `k` start at `CellState.init p.home`, and the actions `acts k` sent at boundary `k` take
`c k` to `c (k + 1)` with the exact sample `(x (k h), v (k h))`. A design model, not from MLS. -/
def IsCellRun (L : Loop.Params 3 Waypoint) (p : Supervisor.Params) (x v : ℝ → Fin 3 → ℝ)
    (c : ℕ → CellState) (acts : ℕ → List Action) : Prop :=
  c 0 = CellState.init p.home ∧
    ∀ k : ℕ, Boundary L p k (x (k * L.period)) (v (k * L.period)) (c k) (acts k) (c (k + 1))

/-- All the actions sent before boundary `k`: `acts 0 ++ … ++ acts (k − 1)`. A design model, not
from MLS. -/
def actsUpTo (acts : ℕ → List Action) : ℕ → List Action
  | 0 => []
  | k + 1 => actsUpTo acts k ++ acts k

/-- Running a concatenation of action lists runs the first and then the second. A design
statement, not from MLS. -/
theorem run_append (p : Supervisor.Params) (s : Supervisor.State) (l₁ l₂ : List Action) :
    run p s (l₁ ++ l₂) = (run p s l₁).bind fun s' => run p s' l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons a l ih =>
    simp only [List.cons_append, run]
    split
    · rfl
    · exact ih _

/-- An accepted step is the action's effect, with its design guards. A design statement, not from
MLS. -/
theorem step_eq_some {p : Supervisor.Params} {s s' : Supervisor.State} {a : Action}
    (h : step p s a = some s') : s' = s.apply a ∧ a.Enabled p s := by
  refine ⟨?_, (step_isSome_iff p s a).mp (by simp [h])⟩
  unfold step at h
  split at h
  · simp at h
  · exact (Option.some.inj h).symm

/-- Queue actions accepted by the supervisor change neither `busy`, `faulted`, `age`, `current`
nor the commanded list. A design statement, not from MLS. -/
theorem run_queue {p : Supervisor.Params} {s s₁ : Supervisor.State} {pre : List Action}
    (hq : ∀ a ∈ pre, IsQueueAction a) (h : run p s pre = some s₁) :
    s₁.busy = s.busy ∧ s₁.faulted = s.faulted ∧ s₁.age = s.age ∧ s₁.current = s.current ∧
      s₁.commanded = s.commanded := by
  induction pre generalizing s with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons a l ih =>
    simp only [run] at h
    split at h
    · simp at h
    · rename_i s₂ h₂
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih (fun b hb => hq b (List.mem_cons_of_mem a hb)) h
      have ha := hq a List.mem_cons_self
      obtain ⟨rfl, -⟩ := step_eq_some h₂
      cases a <;> simp [IsQueueAction] at ha <;> exact ⟨h1, h2, h3, h4, h5⟩

/-- The policy's actions are accepted by the supervisor. A design statement, not from MLS. -/
theorem PolicyStep.run {L : Loop.Params 3 Waypoint} {p : Supervisor.Params} {k : ℕ}
    {θ θ' : Fin 3 → ℝ} {c c' : CellState} {pol : List Action}
    (h : PolicyStep L p k θ θ' c pol c') : run p c.sup pol = some c'.sup := by
  cases h with
  | finish _ _ _ _ hstep => simp [Supervisor.run, hstep]
  | timeout _ _ _ _ hstep => simp [Supervisor.run, hstep]
  | tick _ _ _ _ hstep => simp [Supervisor.run, hstep]
  | wait => rfl
  | admit _ _ _ hstep => simp [Supervisor.run, hstep]

/-- The actions of a boundary are accepted by the supervisor. A design statement, not from MLS. -/
theorem Boundary.run {L : Loop.Params 3 Waypoint} {p : Supervisor.Params} {k : ℕ}
    {θ θ' : Fin 3 → ℝ} {c c' : CellState} {acts : List Action}
    (h : Boundary L p k θ θ' c acts c') : run p c.sup acts = some c'.sup := by
  obtain ⟨pre, pol, s₁, rfl, -, hpre, hpol⟩ := h
  rw [run_append, hpre]
  exact hpol.run

/-- The queue actions leave the loop state of a cell state unchanged. A design statement, not from
MLS. -/
theorem toLoop_queue {p : Supervisor.Params} {c : CellState} {s₁ : Supervisor.State}
    {pre : List Action} (hq : ∀ a ∈ pre, IsQueueAction a) (h : run p c.sup pre = some s₁) :
    ({ c with sup := s₁ } : CellState).toLoop = c.toLoop := by
  obtain ⟨h1, h2, h3, h4, -⟩ := run_queue hq h
  simp [CellState.toLoop, h1, h2, h3, h4]

/-- One boundary keeps the controller's goal as the commanded list while busy. A design
statement, not from MLS. -/
theorem Boundary.commanded_eq {L : Loop.Params 3 Waypoint} {p : Supervisor.Params} {k : ℕ}
    {θ θ' : Fin 3 → ℝ} {c c' : CellState} {acts : List Action}
    (h : Boundary L p k θ θ' c acts c')
    (hc : c.sup.busy = true → c.sup.commanded = [c.goal]) :
    c'.sup.busy = true → c'.sup.commanded = [c'.goal] := by
  obtain ⟨pre, pol, s₁, -, hq, hpre, hpol⟩ := h
  obtain ⟨h1, -, -, -, h5⟩ := run_queue hq hpre
  cases hpol with
  | finish s' _ _ _ hstep =>
    obtain ⟨rfl, -⟩ := step_eq_some hstep
    simp [Supervisor.State.apply]
  | timeout s' _ _ _ hstep =>
    obtain ⟨rfl, -⟩ := step_eq_some hstep
    simp [Supervisor.State.apply]
  | tick s' hbusy _ _ hstep =>
    obtain ⟨rfl, -⟩ := step_eq_some hstep
    intro _
    simp only [Supervisor.State.apply]
    rw [h5]
    exact hc (h1 ▸ hbusy)
  | wait hidle =>
    intro hb
    simp only at hb
    rw [h1] at hb
    simp only [h5]
    exact hc hb
  | admit w s' _ hstep =>
    obtain ⟨rfl, -⟩ := step_eq_some hstep
    intro _
    simp [Supervisor.State.apply]

/-- **One boundary of the cell loop is a step of the loop.** If the loop data's guard contains
the supervisor's link relation and its bound is the supervisor's, and the commanded list is the
goal while busy, then the loop states of a boundary are related by `Loop.Step`. A design
statement, not from MLS. -/
theorem Boundary.toLoop_step {L : Loop.Params 3 Waypoint} {p : Supervisor.Params}
    (hlink : ∀ a b, CellLinked p.cells a b → L.linked a b) (hbound : L.bound = p.bound)
    {k : ℕ} {θ θ' : Fin 3 → ℝ} {c c' : CellState} {acts : List Action}
    (h : Boundary L p k θ θ' c acts c')
    (hc : c.sup.busy = true → c.sup.commanded = [c.goal]) :
    Loop.Step L k θ θ' c.toLoop c'.toLoop := by
  obtain ⟨pre, pol, s₁, -, hq, hpre, hpol⟩ := h
  have hloop := toLoop_queue (c := c) hq hpre
  obtain ⟨h1, h2, h3, h4, h5⟩ := run_queue hq hpre
  rw [← hloop]
  cases hpol with
  | finish s' hbusy hdue harr hstep =>
    obtain ⟨rfl, -⟩ := step_eq_some hstep
    have hcom : s₁.commanded = [c.goal] := h5 ▸ hc (h1 ▸ hbusy)
    have e : ({ c with sup := s₁.apply .finish } : CellState).toLoop =
        { ({ c with sup := s₁ } : CellState).toLoop with
          current := ({ c with sup := s₁ } : CellState).toLoop.goal, busy := false, age := 0 } := by
      simp [CellState.toLoop, Supervisor.State.apply, hcom]
    rw [e]
    exact Loop.Step.finish _ hbusy hdue harr
  | timeout s' hbusy hnot hage hstep =>
    obtain ⟨rfl, -⟩ := step_eq_some hstep
    have e : ({ c with sup := s₁.apply .timeout } : CellState).toLoop =
        { ({ c with sup := s₁ } : CellState).toLoop with
          busy := false, faulted := true, age := 0 } := by
      simp [CellState.toLoop, Supervisor.State.apply]
    rw [e]
    exact Loop.Step.timeout _ hbusy hnot (by rw [hbound]; exact hage)
  | tick s' hbusy hnot hage hstep =>
    obtain ⟨rfl, -⟩ := step_eq_some hstep
    have e : ({ c with sup := s₁.apply .tick } : CellState).toLoop =
        { ({ c with sup := s₁ } : CellState).toLoop with
          age := ({ c with sup := s₁ } : CellState).toLoop.age + 1 } := by
      simp [CellState.toLoop, Supervisor.State.apply]
    rw [e]
    exact Loop.Step.tick _ hbusy hnot (by rw [hbound]; exact hage)
  | wait hidle => exact Loop.Step.wait _ hidle
  | admit w s' hidle hstep =>
    obtain ⟨rfl, hen⟩ := step_eq_some hstep
    obtain ⟨-, -, hok, hlinked⟩ := hen
    convert Loop.Step.admit ({ c with sup := s₁ } : CellState).toLoop w hidle hok
      (hlink _ _ hlinked) using 1
    simp [CellState.toLoop, Supervisor.State.apply]

/-- **The executable supervisor's state is the result of `run`.** Along a timed run of the cell
loop, the supervisor's state before boundary `k` is `run p (State.init p.home)` of all the actions
sent before `k`. A design statement, not from MLS. -/
theorem IsCellRun.run_eq {L : Loop.Params 3 Waypoint} {p : Supervisor.Params}
    {x v : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (h : IsCellRun L p x v c acts) (k : ℕ) :
    run p (Supervisor.State.init p.home) (actsUpTo acts k) = some (c k).sup := by
  induction k with
  | zero => rw [h.1]; rfl
  | succ k ih =>
    rw [actsUpTo, run_append, ih]
    exact (h.2 k).run

/-- Along a timed run of the cell loop, the commanded list is the controller's goal while busy. A
design statement, not from MLS. -/
theorem IsCellRun.commanded_eq {L : Loop.Params 3 Waypoint} {p : Supervisor.Params}
    {x v : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (h : IsCellRun L p x v c acts) (k : ℕ) :
    (c k).sup.busy = true → (c k).sup.commanded = [(c k).goal] := by
  induction k with
  | zero => rw [h.1]; simp [CellState.init, Supervisor.State.init]
  | succ k ih => exact (h.2 k).commanded_eq ih

/-- **A timed run of the cell loop is a timed run of the loop.** For loop data whose guard
contains the supervisor's link relation `CellLinked p.cells` and whose bound is `p.bound`, the
loop states of a timed run of the cell loop form a timed run of the loop from `p.home`. A design
statement, not from MLS. -/
theorem IsCellRun.isRun {L : Loop.Params 3 Waypoint} {p : Supervisor.Params}
    (hlink : ∀ a b, CellLinked p.cells a b → L.linked a b) (hbound : L.bound = p.bound)
    {x v : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (h : IsCellRun L p x v c acts) :
    Loop.IsRun L p.home x v (fun k => (c k).toLoop) :=
  ⟨by show (c 0).toLoop = _; rw [h.1]; rfl,
    fun k => (h.2 k).toLoop_step hlink hbound (h.commanded_eq k)⟩

end RoboLean.Cell.Loop
