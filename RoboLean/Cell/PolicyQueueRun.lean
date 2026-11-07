import RoboLean.Cell.PolicyQueue
import RoboLean.Cell.SupervisorQueue
import RoboLean.Cell.PolicyRun
import RoboLean.Cell.AssuredMeasuredGain50

/-!
# The program on the queue supervisor and the assured cell

The policy program `RoboLean.Cell.PolicyQueue.boundary` on the queue supervisor of
`RoboLean.Cell.SupervisorQueue`, read in the units of the loop model, and the assured cell with the
program's run as its hypothesis. The loop states are the cell states `CellState` of
`RoboLean.Cell.LoopSupervisor`, reused unchanged: the supervisor's state (its list `requested` read
as the queue) and the controller's record of the last admitted move.

* `QueuePolicyStep`, `QueueBoundary`, `IsMeasuredQueueCellRun`, `queueActsUpTo`: the policy's
  action, a boundary (requests forwarded, then the policy's action, each accepted by the queue
  supervisor's `step`), the timed runs of the cell loop on measured samples and the actions sent so
  far, for the queue supervisor.
* `IsMeasuredQueueCellRun.run_eq_apply`, `IsMeasuredQueueCellRun.commanded_eq_apply`,
  `IsMeasuredQueueCellRun.isMeasuredOpenRun`: the supervisor's state is `SupervisorQueue.run` of
  the actions sent so far, the commanded list is the goal while busy, and the loop states form a
  measured run of the open loop, by the effects of the accepted actions only.
* `IsMeasuredQueueCellRun.loopContract`: the queue supervisor's contract gives the loop-level
  contract. The queue supervisor's `admit` has no link test, so that every admitted move is linked
  comes from the contract only.
* `queue_boundary_spec`, `PolicyQueue.IsProgramRun.isMeasuredCellRun`: every output of the program
  is a boundary step, so the program's runs are measured timed runs of the cell loop.
* `cell_measured_hyps_queue`, `cell_assured_measured_right_queue`: the assured cell on measured
  samples for the queue supervisor.
* `PolicyQueue.designNominalGain50`, `designNominalGain50_queue_loop`,
  `cell_assured_program_measured_gain50_queue` and its exact-sample variant: the gain-50 design
  point with the program's run on the queue supervisor as hypothesis.

The queue supervisor's contract `SupervisorQueue.Contract` stays a premise. The arm is `cellArm`
(MLS Example 4.3, printed p. 172) under computed torque (MLS eq. (4.49), p. 191), with right
derivatives only. The program, the configuration, the loop and the bounds are design statements,
not from MLS. Seconds, radians, radians per second; waypoints in rational degrees. The statements
concern the ideal rigid-body model with a bounded disturbance and the sampled loop with a bounded
sample error, not a physical arm, and the compiled program only through the Lean definitions it is
built from.
-/

namespace RoboLean.Cell.PolicyQueue

/-- The policy program's configuration on the queue supervisor at the gain-50 design point: the
configuration `Policy.designNominalGain50` (the cell's supervisor parameters, period `1/10` s, move
duration `2` s, position tolerance `3` degrees, speed tolerance `33/10` rad/s, encoders of `2^18`
counts per revolution) and a queue of capacity `8`. A design definition, not from MLS. -/
def designNominalGain50 : Config :=
  { Policy.designNominalGain50 with capacity := 8 }

end RoboLean.Cell.PolicyQueue

noncomputable section

namespace RoboLean.Cell.Loop

open Set Supervisor

/-! ### The queue supervisor in the sampled loop -/

/-- The request actions of a boundary for the queue supervisor: `request w prio`, which changes only
the supervisor's queue and rejection list. A design model, not from MLS. -/
def IsRequestAction : SupervisorQueue.Action → Prop
  | .request _ _ => True
  | _ => False

/-- The policy's action at boundary `k` from the sample `(θ, θ')`, sent to the queue supervisor
with parameters `p` after the requests: `finish`, `timeout` or `tick` while busy as in `Loop.Step`,
nothing or `admit` while idle; each action is accepted by `SupervisorQueue.step`, and an admission,
which takes the queue's head `h`, records the move from the current waypoint to `h` admitted at
`k`. A design model, not from MLS. -/
inductive QueuePolicyStep (L : Loop.Params 3 Waypoint) (p : SupervisorQueue.Params) (k : ℕ)
    (θ θ' : Fin 3 → ℝ) : CellState → List SupervisorQueue.Action → CellState → Prop
  /-- Busy, due and arrived: `finish`. -/
  | finish (c : CellState) (s' : Supervisor.State) (hbusy : c.sup.busy = true)
      (hdue : Due L c.toLoop k) (harr : Arrived L c.goal θ θ')
      (hstep : SupervisorQueue.step p c.sup .finish = some s') :
      QueuePolicyStep L p k θ θ' c [.finish] { c with sup := s' }
  /-- Busy, not finished, age at the bound: `timeout`. -/
  | timeout (c : CellState) (s' : Supervisor.State) (hbusy : c.sup.busy = true)
      (hnot : ¬ (Due L c.toLoop k ∧ Arrived L c.goal θ θ')) (hage : c.sup.age = p.bound)
      (hstep : SupervisorQueue.step p c.sup .timeout = some s') :
      QueuePolicyStep L p k θ θ' c [.timeout] { c with sup := s' }
  /-- Busy, not finished, age not at the bound: `tick`. -/
  | tick (c : CellState) (s' : Supervisor.State) (hbusy : c.sup.busy = true)
      (hnot : ¬ (Due L c.toLoop k ∧ Arrived L c.goal θ θ')) (hage : c.sup.age ≠ p.bound)
      (hstep : SupervisorQueue.step p c.sup .tick = some s') :
      QueuePolicyStep L p k θ θ' c [.tick] { c with sup := s' }
  /-- Idle: no action. -/
  | wait (c : CellState) (hidle : c.sup.busy = false) : QueuePolicyStep L p k θ θ' c [] c
  /-- Idle, the queue's head is `h`: `admit`, accepted by the queue supervisor. -/
  | admit (c : CellState) (h : Waypoint) (rest : List Waypoint) (s' : Supervisor.State)
      (hidle : c.sup.busy = false) (hq : c.sup.requested = h :: rest)
      (hstep : SupervisorQueue.step p c.sup .admit = some s') :
      QueuePolicyStep L p k θ θ' c [.admit] ⟨s', c.sup.current, h, k⟩

/-- One boundary `k` of the cell loop with the queue supervisor and the sample `(θ, θ')`: the
actions `acts` are requests `pre`, accepted by `SupervisorQueue.run`, followed by the policy's
action `pol`. A design model, not from MLS. -/
def QueueBoundary (L : Loop.Params 3 Waypoint) (p : SupervisorQueue.Params) (k : ℕ)
    (θ θ' : Fin 3 → ℝ) (c : CellState) (acts : List SupervisorQueue.Action) (c' : CellState) :
    Prop :=
  ∃ pre pol : List SupervisorQueue.Action, ∃ s₁ : Supervisor.State, acts = pre ++ pol ∧
    (∀ a ∈ pre, IsRequestAction a) ∧ SupervisorQueue.run p c.sup pre = some s₁ ∧
    QueuePolicyStep L p k θ θ' { c with sup := s₁ } pol c'

/-- A timed run of the cell loop with the queue supervisor on measured samples: the loop states
`c k` before the boundary `k` start at `CellState.init p.home`, and the actions `acts k` sent at
boundary `k` take `c k` to `c (k + 1)` with the measured sample `(xm k, vm k)` (rad, rad/s) taken at
the boundary `k h`. A design model, not from MLS. -/
def IsMeasuredQueueCellRun (L : Loop.Params 3 Waypoint) (p : SupervisorQueue.Params)
    (xm vm : ℕ → Fin 3 → ℝ) (c : ℕ → CellState) (acts : ℕ → List SupervisorQueue.Action) :
    Prop :=
  c 0 = CellState.init p.home ∧
    ∀ k : ℕ, QueueBoundary L p k (xm k) (vm k) (c k) (acts k) (c (k + 1))

/-- All the actions sent to the queue supervisor before boundary `k`:
`acts 0 ++ … ++ acts (k − 1)`. A design model, not from MLS. -/
def queueActsUpTo (acts : ℕ → List SupervisorQueue.Action) : ℕ → List SupervisorQueue.Action
  | 0 => []
  | k + 1 => queueActsUpTo acts k ++ acts k

/-- An accepted step of the queue supervisor is the action's effect `SupervisorQueue.effect`;
nothing is said about when the step is accepted. A design statement, not from MLS. -/
theorem queue_step_eq_effect {p : SupervisorQueue.Params} {s s' : Supervisor.State}
    {a : SupervisorQueue.Action} (h : SupervisorQueue.step p s a = some s') :
    s' = SupervisorQueue.effect p s a := by
  unfold SupervisorQueue.step at h
  split at h
  · simp at h
  · exact (Option.some.inj h).symm

/-- `SupervisorQueue.run` on a nonempty list takes the first step and runs the rest from its
result. A design statement, not from MLS. -/
theorem queue_run_cons (p : SupervisorQueue.Params) (s : Supervisor.State)
    (a : SupervisorQueue.Action) (l : List SupervisorQueue.Action) :
    SupervisorQueue.run p s (a :: l) =
      (SupervisorQueue.step p s a).bind fun s' => SupervisorQueue.run p s' l := by
  cases h : SupervisorQueue.step p s a with
  | none =>
    show (match SupervisorQueue.step p s a with
      | none => none | some s' => SupervisorQueue.run p s' l) = none
    rw [h]
  | some s' =>
    show (match SupervisorQueue.step p s a with
      | none => none | some s' => SupervisorQueue.run p s' l) = SupervisorQueue.run p s' l
    rw [h]

/-- Running a concatenation of action lists on the queue supervisor runs the first and then the
second. A design statement, not from MLS. -/
theorem queue_run_append (p : SupervisorQueue.Params) (s : Supervisor.State)
    (l₁ l₂ : List SupervisorQueue.Action) :
    SupervisorQueue.run p s (l₁ ++ l₂) =
      (SupervisorQueue.run p s l₁).bind fun s' => SupervisorQueue.run p s' l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons a l ih =>
    rw [List.cons_append, queue_run_cons, queue_run_cons]
    cases SupervisorQueue.step p s a with
    | none => rfl
    | some s' => exact ih s'

/-- A single accepted action of the queue supervisor runs to its result. A design statement, not
from MLS. -/
theorem queue_run_singleton_of_step {p : SupervisorQueue.Params} {s s' : Supervisor.State}
    {a : SupervisorQueue.Action} (h : SupervisorQueue.step p s a = some s') :
    SupervisorQueue.run p s [a] = some s' := by
  rw [queue_run_cons, h]
  rfl

/-- The effect of a request, queued or rejected, changes neither `busy`, `faulted`, `age`,
`current` nor the commanded list. A design statement, not from MLS. -/
theorem queue_effect_request (p : SupervisorQueue.Params) (s : Supervisor.State) (w : Waypoint)
    (prio : SupervisorQueue.Priority) :
    (SupervisorQueue.effect p s (.request w prio)).busy = s.busy ∧
      (SupervisorQueue.effect p s (.request w prio)).faulted = s.faulted ∧
      (SupervisorQueue.effect p s (.request w prio)).age = s.age ∧
      (SupervisorQueue.effect p s (.request w prio)).current = s.current ∧
      (SupervisorQueue.effect p s (.request w prio)).commanded = s.commanded := by
  by_cases hq : SupervisorQueue.queueable p s w prio = true <;> cases prio <;>
    simp [SupervisorQueue.effect, hq]

/-- Requests accepted by the queue supervisor change neither `busy`, `faulted`, `age`, `current`
nor the commanded list, by their effects alone. A design statement, not from MLS. -/
theorem queue_run_request_apply {p : SupervisorQueue.Params} {s s₁ : Supervisor.State}
    {pre : List SupervisorQueue.Action} (hq : ∀ a ∈ pre, IsRequestAction a)
    (h : SupervisorQueue.run p s pre = some s₁) :
    s₁.busy = s.busy ∧ s₁.faulted = s.faulted ∧ s₁.age = s.age ∧ s₁.current = s.current ∧
      s₁.commanded = s.commanded := by
  induction pre generalizing s with
  | nil =>
    have h' : some s = some s₁ := h
    obtain rfl := Option.some.inj h'
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons a l ih =>
    rw [queue_run_cons] at h
    cases h₂ : SupervisorQueue.step p s a with
    | none =>
      rw [h₂] at h
      exact absurd h (by simp)
    | some s₂ =>
      rw [h₂] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih (fun b hb => hq b (List.mem_cons_of_mem a hb)) h
      have ha := hq a List.mem_cons_self
      obtain rfl := queue_step_eq_effect h₂
      cases a with
      | request w prio =>
        obtain ⟨e1, e2, e3, e4, e5⟩ := queue_effect_request p s w prio
        exact ⟨h1.trans e1, h2.trans e2, h3.trans e3, h4.trans e4, h5.trans e5⟩
      | _ => exact absurd ha (by simp [IsRequestAction])

/-- The policy's actions are accepted by the queue supervisor and run to the next state. A design
statement, not from MLS. -/
theorem QueuePolicyStep.run_apply {L : Loop.Params 3 Waypoint} {p : SupervisorQueue.Params}
    {k : ℕ} {θ θ' : Fin 3 → ℝ} {c c' : CellState} {pol : List SupervisorQueue.Action}
    (h : QueuePolicyStep L p k θ θ' c pol c') : SupervisorQueue.run p c.sup pol = some c'.sup := by
  cases h with
  | finish _ _ _ _ hstep => exact queue_run_singleton_of_step hstep
  | timeout _ _ _ _ hstep => exact queue_run_singleton_of_step hstep
  | tick _ _ _ _ hstep => exact queue_run_singleton_of_step hstep
  | wait => rfl
  | admit _ _ _ _ _ hstep => exact queue_run_singleton_of_step hstep

/-- The actions of a boundary run the queue supervisor's state to the next one. A design
statement, not from MLS. -/
theorem QueueBoundary.run_apply {L : Loop.Params 3 Waypoint} {p : SupervisorQueue.Params} {k : ℕ}
    {θ θ' : Fin 3 → ℝ} {c c' : CellState} {acts : List SupervisorQueue.Action}
    (h : QueueBoundary L p k θ θ' c acts c') : SupervisorQueue.run p c.sup acts = some c'.sup := by
  obtain ⟨pre, pol, s₁, rfl, -, hpre, hpol⟩ := h
  rw [queue_run_append, hpre]
  exact hpol.run_apply

/-- **The queue supervisor's state is the result of `run`, on measured samples.** Along a timed run
of the cell loop with the queue supervisor on measured samples, the supervisor's state before
boundary `k` is `SupervisorQueue.run p (State.init p.home)` of all the actions sent before `k`. A
design statement, not from MLS. -/
theorem IsMeasuredQueueCellRun.run_eq_apply {L : Loop.Params 3 Waypoint}
    {p : SupervisorQueue.Params} {xm vm : ℕ → Fin 3 → ℝ} {c : ℕ → CellState}
    {acts : ℕ → List SupervisorQueue.Action} (h : IsMeasuredQueueCellRun L p xm vm c acts) (k : ℕ) :
    SupervisorQueue.run p (Supervisor.State.init p.home) (queueActsUpTo acts k) =
      some (c k).sup := by
  induction k with
  | zero => rw [h.1]; rfl
  | succ k ih =>
    rw [queueActsUpTo, queue_run_append, ih]
    exact (h.2 k).run_apply

/-- One boundary with the queue supervisor keeps the controller's goal as the commanded list while
busy, by the effects of the accepted actions. A design statement, not from MLS. -/
theorem QueueBoundary.commanded_eq_apply {L : Loop.Params 3 Waypoint} {p : SupervisorQueue.Params}
    {k : ℕ} {θ θ' : Fin 3 → ℝ} {c c' : CellState} {acts : List SupervisorQueue.Action}
    (h : QueueBoundary L p k θ θ' c acts c')
    (hc : c.sup.busy = true → c.sup.commanded = [c.goal]) :
    c'.sup.busy = true → c'.sup.commanded = [c'.goal] := by
  obtain ⟨pre, pol, s₁, -, hq, hpre, hpol⟩ := h
  obtain ⟨h1, -, -, -, h5⟩ := queue_run_request_apply hq hpre
  cases hpol with
  | finish s' _ _ _ hstep =>
    obtain rfl := queue_step_eq_effect hstep
    simp [SupervisorQueue.effect]
  | timeout s' _ _ _ hstep =>
    obtain rfl := queue_step_eq_effect hstep
    simp [SupervisorQueue.effect]
  | tick s' hbusy _ _ hstep =>
    obtain rfl := queue_step_eq_effect hstep
    intro _
    simp only [SupervisorQueue.effect]
    rw [h5]
    exact hc (h1 ▸ hbusy)
  | wait hidle =>
    intro hb
    simp only at hb
    rw [h1] at hb
    simp only [h5]
    exact hc hb
  | admit w rest s' _ hreq hstep =>
    obtain rfl := queue_step_eq_effect hstep
    have hreq' : s₁.requested = w :: rest := hreq
    intro _
    simp [SupervisorQueue.effect, hreq']

/-- Along a timed run of the cell loop with the queue supervisor on measured samples, the commanded
list is the controller's goal while busy, by the effects of the accepted actions. A design
statement, not from MLS. -/
theorem IsMeasuredQueueCellRun.commanded_eq_apply {L : Loop.Params 3 Waypoint}
    {p : SupervisorQueue.Params} {xm vm : ℕ → Fin 3 → ℝ} {c : ℕ → CellState}
    {acts : ℕ → List SupervisorQueue.Action} (h : IsMeasuredQueueCellRun L p xm vm c acts) (k : ℕ) :
    (c k).sup.busy = true → (c k).sup.commanded = [(c k).goal] := by
  induction k with
  | zero => rw [h.1]; simp [CellState.init, Supervisor.State.init]
  | succ k ih => exact (h.2 k).commanded_eq_apply ih

/-- **One boundary with the queue supervisor is a step of the open loop.** If the loop data's bound
is the supervisor's and the commanded list is the goal while busy, the loop states of a boundary are
related by `OpenStep`; only the effects of the accepted actions are used. A design statement, not
from MLS. -/
theorem QueueBoundary.toOpenStep {L : Loop.Params 3 Waypoint} {p : SupervisorQueue.Params}
    (hbound : L.bound = p.bound) {k : ℕ} {θ θ' : Fin 3 → ℝ} {c c' : CellState}
    {acts : List SupervisorQueue.Action} (h : QueueBoundary L p k θ θ' c acts c')
    (hc : c.sup.busy = true → c.sup.commanded = [c.goal]) :
    OpenStep L k θ θ' c.toLoop c'.toLoop := by
  obtain ⟨pre, pol, s₁, -, hq, hpre, hpol⟩ := h
  obtain ⟨h1, h2, h3, h4, h5⟩ := queue_run_request_apply hq hpre
  have hloop : ({ c with sup := s₁ } : CellState).toLoop = c.toLoop := by
    simp [CellState.toLoop, h1, h2, h3, h4]
  rw [← hloop]
  cases hpol with
  | finish s' hbusy hdue harr hstep =>
    obtain rfl := queue_step_eq_effect hstep
    have hcom : s₁.commanded = [c.goal] := h5 ▸ hc (h1 ▸ hbusy)
    have e : ({ c with sup := SupervisorQueue.effect p s₁ .finish } : CellState).toLoop =
        { ({ c with sup := s₁ } : CellState).toLoop with
          current := ({ c with sup := s₁ } : CellState).toLoop.goal, busy := false, age := 0 } := by
      simp [CellState.toLoop, SupervisorQueue.effect, hcom]
    rw [e]
    exact OpenStep.finish _ hbusy hdue harr
  | timeout s' hbusy hnot hage hstep =>
    obtain rfl := queue_step_eq_effect hstep
    have e : ({ c with sup := SupervisorQueue.effect p s₁ .timeout } : CellState).toLoop =
        { ({ c with sup := s₁ } : CellState).toLoop with
          busy := false, faulted := true, age := 0 } := by
      simp [CellState.toLoop, SupervisorQueue.effect]
    rw [e]
    exact OpenStep.timeout _ hbusy hnot (by rw [hbound]; exact hage)
  | tick s' hbusy hnot hage hstep =>
    obtain rfl := queue_step_eq_effect hstep
    have e : ({ c with sup := SupervisorQueue.effect p s₁ .tick } : CellState).toLoop =
        { ({ c with sup := s₁ } : CellState).toLoop with
          age := ({ c with sup := s₁ } : CellState).toLoop.age + 1 } := by
      simp [CellState.toLoop, SupervisorQueue.effect]
    rw [e]
    exact OpenStep.tick _ hbusy hnot (by rw [hbound]; exact hage)
  | wait hidle => exact OpenStep.wait _ hidle
  | admit w rest s' hidle hreq hstep =>
    obtain rfl := queue_step_eq_effect hstep
    have hreq' : s₁.requested = w :: rest := hreq
    convert OpenStep.admit ({ c with sup := s₁ } : CellState).toLoop w hidle using 1
    simp [CellState.toLoop, SupervisorQueue.effect, hreq']

/-- **A timed run of the cell loop with the queue supervisor on measured samples is a measured run
of the open loop.** For loop data whose bound is the supervisor's, the loop states form a timed run
of the open loop from `p.home` on the same measured samples; no guard of the supervisor is used. A
design statement, not from MLS. -/
theorem IsMeasuredQueueCellRun.isMeasuredOpenRun {L : Loop.Params 3 Waypoint}
    {p : SupervisorQueue.Params} {xm vm : ℕ → Fin 3 → ℝ} {c : ℕ → CellState}
    {acts : ℕ → List SupervisorQueue.Action} (hbound : L.bound = p.bound)
    (h : IsMeasuredQueueCellRun L p xm vm c acts) :
    IsMeasuredOpenRun L p.home xm vm (fun k => (c k).toLoop) :=
  ⟨by show (c 0).toLoop = _; rw [h.1]; rfl,
    fun k => (h.2 k).toOpenStep hbound (h.commanded_eq_apply k)⟩

/-- **The queue supervisor's contract gives the loop-level contract, on measured samples.** Along
a timed run of the cell loop with the queue supervisor on measured samples, the supervisor's state
before boundary `k` is `SupervisorQueue.run` of the actions sent so far; the contract's sixth clause
links every commanded waypoint, in particular the goal of a busy loop, to the waypoint the arm is
at, and its fifth clause makes a faulted supervisor idle. The queue supervisor's `admit` has no link
test, so the link of an admitted move comes from the contract only. For loop data whose link
relation contains the program's link test, the loop states meet `LoopContract`. A design statement,
not from MLS. -/
theorem IsMeasuredQueueCellRun.loopContract {L : Loop.Params 3 Waypoint}
    {p : SupervisorQueue.Params} {xm vm : ℕ → Fin 3 → ℝ} {c : ℕ → CellState}
    {acts : ℕ → List SupervisorQueue.Action} (hsup : SupervisorQueue.Contract p)
    (hlink : ∀ a b, Supervisor.linked p.cells a b = true → L.linked a b)
    (h : IsMeasuredQueueCellRun L p xm vm c acts) : LoopContract L (fun k => (c k).toLoop) :=
  fun k => by
    obtain ⟨-, -, -, -, h5, h6⟩ := hsup _ _ (h.run_eq_apply k)
    refine ⟨fun hb => hlink _ _ (h6 _ ?_), h5⟩
    rw [h.commanded_eq_apply k hb]
    exact List.mem_singleton_self _

end RoboLean.Cell.Loop

namespace RoboLean.Cell.PolicyQueue

open RoboLean.Cell.Supervisor RoboLean.Cell.Loop

/-- The cell loop state of a policy state on the queue supervisor: the supervisor's state and the
controller's record of the last admitted move. A design model, not from MLS. -/
def State.toCell (st : State) : CellState :=
  ⟨st.sup, st.src, st.goal, st.start⟩

end RoboLean.Cell.PolicyQueue

namespace RoboLean.Cell.Loop

open Set Supervisor

/-- The forwarded requests are request actions. A design statement, not from MLS. -/
theorem requestActions_isRequest (reqs : List (Waypoint × SupervisorQueue.Priority)) :
    ∀ a ∈ PolicyQueue.requestActions reqs, IsRequestAction a := by
  intro a ha
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha
  trivial

/-- **Every output of the program on the queue supervisor is a boundary step of the cell loop.**
If the policy program at boundary `k`, with the requests `reqs` and the sample `smp`, takes the
state `st` to `st'` with the actions `acts`, then `acts` and the cell states of `st` and `st'` form
a `QueueBoundary` step for the loop data `cfg.toConfig.loop`, the queue supervisor's parameters
`cfg.qsup` and the sample read in radians and rad/s. A design statement, not from MLS. -/
theorem queue_boundary_spec {cfg : PolicyQueue.Config} {k : ℕ}
    {reqs : List (Waypoint × SupervisorQueue.Priority)} {smp : Policy.Sample}
    {st st' : PolicyQueue.State} {acts : List SupervisorQueue.Action}
    (h : PolicyQueue.boundary cfg k reqs smp st = some (acts, st')) :
    QueueBoundary cfg.toConfig.loop cfg.qsup k (smp.toRad cfg.toConfig) smp.velRad st.toCell acts
      st'.toCell := by
  have hpre := requestActions_isRequest reqs
  unfold PolicyQueue.boundary at h
  split at h
  · exact absurd h (by simp)
  · rename_i s₁ hs₁
    split at h
    · -- busy: the busy action
      rename_i hbusy
      split at h
      · exact absurd h (by simp)
      · rename_i s' hs'
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨_, _, s₁, rfl, hpre, hs₁, ?_⟩
        set st₁ : PolicyQueue.State := { st with sup := s₁ } with hst₁
        have hc : ({ st.toCell with sup := s₁ } : CellState) = st₁.toPolicy.toCell := rfl
        have hc' : ({ st with sup := s' } : PolicyQueue.State).toCell =
            { st₁.toPolicy.toCell with sup := s' } := rfl
        have hb : st₁.toPolicy.toCell.sup.busy = true := hbusy
        rw [hc, hc']
        unfold PolicyQueue.busyAction at hs' ⊢
        by_cases hfin : (Policy.due cfg.toConfig st₁.toPolicy k &&
            Policy.arrived cfg.toConfig st₁.goal smp) = true
        · simp only [hfin, ↓reduceIte] at hs' ⊢
          rw [Bool.and_eq_true] at hfin
          exact QueuePolicyStep.finish _ s' hb (due_eq_true_iff.mp hfin.1)
            (arrived_eq_true_iff.mp hfin.2) hs'
        · have hnot : ¬ (Due cfg.toConfig.loop st₁.toPolicy.toCell.toLoop k ∧
              Arrived cfg.toConfig.loop st₁.toPolicy.toCell.goal (smp.toRad cfg.toConfig)
                smp.velRad) := by
            rintro ⟨h1, h2⟩
            exact hfin (by rw [Bool.and_eq_true]; exact ⟨due_eq_true_iff.mpr h1,
              arrived_eq_true_iff.mpr h2⟩)
          simp only [hfin, Bool.false_eq_true, ↓reduceIte] at hs' ⊢
          by_cases hage : st₁.sup.age = cfg.sup.bound
          · simp only [hage, ↓reduceIte] at hs' ⊢
            exact QueuePolicyStep.timeout _ s' hb hnot hage hs'
          · simp only [hage, ↓reduceIte] at hs' ⊢
            exact QueuePolicyStep.tick _ s' hb hnot hage hs'
    · rename_i hidle
      have hidle' : s₁.busy = false := by simpa using hidle
      split at h
      · -- idle and faulted: nothing
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, [], s₁, (List.append_nil _).symm, hpre, hs₁, QueuePolicyStep.wait _ hidle'⟩
      · split at h
        · -- idle, empty queue: nothing
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨_, [], s₁, (List.append_nil _).symm, hpre, hs₁, QueuePolicyStep.wait _ hidle'⟩
        · -- idle, not faulted, the queue's head `w`: admit
          rename_i w rest hreq
          split at h
          · exact absurd h (by simp)
          · rename_i s₂ hs₂
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨_, _, s₁, rfl, hpre, hs₁, QueuePolicyStep.admit _ w rest s₂ hidle' hreq hs₂⟩

/-- **A run of the program on the queue supervisor is a measured timed run of the cell loop.** The
cell states of the program's states and the program's actions form a timed run of the cell loop
with the queue supervisor on the program's own samples, read in radians and rad/s; nothing is
assumed about the true state. A design statement, not from MLS. -/
theorem _root_.RoboLean.Cell.PolicyQueue.IsProgramRun.isMeasuredCellRun {cfg : PolicyQueue.Config}
    {reqs : ℕ → List (Waypoint × SupervisorQueue.Priority)} {smp : ℕ → Policy.Sample}
    {st : ℕ → PolicyQueue.State} {acts : ℕ → List SupervisorQueue.Action}
    (h : PolicyQueue.IsProgramRun cfg reqs smp st acts) :
    IsMeasuredQueueCellRun cfg.toConfig.loop cfg.qsup (fun k => (smp k).toRad cfg.toConfig)
      (fun k => (smp k).velRad) (fun k => (st k).toCell) acts :=
  ⟨by show (st 0).toCell = _; rw [h.1]; rfl, fun k => queue_boundary_spec (h.2 k)⟩

/-! ### The program on the queue supervisor never blocks one of its own actions -/

/-- An action whose guards all hold (`SupervisorQueue.Action.blocker` returns `none`) is accepted
by the queue supervisor's `step`, with its effect `SupervisorQueue.effect`. A design statement, not
from MLS. -/
theorem queue_step_eq_some_of_blocker {p : SupervisorQueue.Params} {s : Supervisor.State}
    {a : SupervisorQueue.Action} (h : a.blocker p s = none) :
    SupervisorQueue.step p s a = some (SupervisorQueue.effect p s a) := by
  unfold SupervisorQueue.step
  rw [h]

/-- A request is accepted by the queue supervisor unless it is busy with no commanded waypoint. A
design statement, not from MLS. -/
theorem queue_blocker_request {p : SupervisorQueue.Params} {s : Supervisor.State} {w : Waypoint}
    {prio : SupervisorQueue.Priority} (hc : s.busy = true → s.commanded ≠ []) :
    (SupervisorQueue.Action.request w prio).blocker p s = none := by
  show (if (s.busy && s.commanded.isEmpty) = true then some "no-command" else none) = none
  cases hb : s.busy
  · simp
  · simp [List.isEmpty_iff, hc hb]

/-- `admit` is accepted by an idle queue supervisor that is not faulted and whose queue is not
empty. A design statement, not from MLS. -/
theorem queue_blocker_admit {p : SupervisorQueue.Params} {s : Supervisor.State}
    (hq : s.requested ≠ []) (hb : s.busy = false) (hf : s.faulted = false) :
    SupervisorQueue.Action.admit.blocker p s = none := by
  show (if s.requested.isEmpty then some "empty"
    else if s.busy = true then some "not-idle"
    else if s.faulted = true then some "faulted" else none) = none
  simp [List.isEmpty_iff, hq, hb, hf]

/-- `finish` is accepted by a busy queue supervisor with a commanded waypoint. A design statement,
not from MLS. -/
theorem queue_blocker_finish {p : SupervisorQueue.Params} {s : Supervisor.State}
    (hb : s.busy = true) (hc : s.commanded ≠ []) :
    SupervisorQueue.Action.finish.blocker p s = none := by
  show (if s.busy = false then some "not-busy"
    else if s.commanded.isEmpty then some "no-command" else none) = none
  simp [hb, List.isEmpty_iff, hc]

/-- `tick` is accepted by a busy queue supervisor whose age is below the bound. A design statement,
not from MLS. -/
theorem queue_blocker_tick {p : SupervisorQueue.Params} {s : Supervisor.State}
    (hb : s.busy = true) (ha : s.age < p.bound) :
    SupervisorQueue.Action.tick.blocker p s = none := by
  show (if s.busy = false then some "not-busy"
    else if s.age < p.bound then none else some "age-at-bound") = none
  simp [hb, ha]

/-- `timeout` is accepted by a busy queue supervisor whose age is the bound. A design statement,
not from MLS. -/
theorem queue_blocker_timeout {p : SupervisorQueue.Params} {s : Supervisor.State}
    (hb : s.busy = true) (ha : s.age = p.bound) :
    SupervisorQueue.Action.timeout.blocker p s = none := by
  show (if s.busy = false then some "not-busy"
    else if s.age = p.bound then none else some "age-not-at-bound") = none
  simp [hb, ha]

/-- The forwarded requests never block: from a state with a commanded waypoint while busy, the
queue supervisor runs every list of forwarded requests to some state. A design statement, not from
MLS. -/
theorem queue_run_requests_isSome (p : SupervisorQueue.Params) :
    ∀ (reqs : List (Waypoint × SupervisorQueue.Priority)) (s : Supervisor.State),
      (s.busy = true → s.commanded ≠ []) →
      ∃ s₁, SupervisorQueue.run p s (PolicyQueue.requestActions reqs) = some s₁ := by
  intro reqs
  induction reqs with
  | nil => intro s _; exact ⟨s, rfl⟩
  | cons r rs ih =>
    intro s hc
    have hstep : SupervisorQueue.step p s (.request r.1 r.2) =
        some (SupervisorQueue.effect p s (.request r.1 r.2)) :=
      queue_step_eq_some_of_blocker (queue_blocker_request hc)
    obtain ⟨e1, -, -, -, e5⟩ := queue_effect_request p s r.1 r.2
    obtain ⟨s₁, hs₁⟩ := ih (SupervisorQueue.effect p s (.request r.1 r.2))
      (fun hb => by rw [e5]; exact hc (by rw [← e1]; exact hb))
    refine ⟨s₁, ?_⟩
    show SupervisorQueue.run p s (.request r.1 r.2 :: PolicyQueue.requestActions rs) = some s₁
    rw [queue_run_cons, hstep]
    exact hs₁

/-- **The program on the queue supervisor never blocks one of its own actions.** From a state whose
supervisor has a commanded waypoint while busy and an age at most the bound (two clauses of the
queue supervisor's contract), the policy program returns a result at every boundary, for every
request list and every sample. A design statement, not from MLS. -/
theorem queue_boundary_isSome {cfg : PolicyQueue.Config} {k : ℕ}
    {reqs : List (Waypoint × SupervisorQueue.Priority)} {smp : Policy.Sample}
    {st : PolicyQueue.State} (hc : st.sup.busy = true → st.sup.commanded ≠ [])
    (ha : st.sup.age ≤ cfg.sup.bound) :
    ∃ r, PolicyQueue.boundary cfg k reqs smp st = some r := by
  obtain ⟨s₁, hs₁⟩ := queue_run_requests_isSome cfg.qsup reqs st.sup hc
  obtain ⟨h1, h2, h3, -, h5⟩ := queue_run_request_apply (requestActions_isRequest reqs) hs₁
  by_cases hb : s₁.busy = true
  · have hc₁ : s₁.commanded ≠ [] := by rw [h5]; exact hc (by rw [← h1]; exact hb)
    have ha₁ : s₁.age ≤ cfg.sup.bound := by rw [h3]; exact ha
    have hs : ∃ s', SupervisorQueue.step cfg.qsup s₁
        (PolicyQueue.busyAction cfg k { st with sup := s₁ } smp) = some s' := by
      unfold PolicyQueue.busyAction
      split_ifs with h₁ h₂
      · exact ⟨_, queue_step_eq_some_of_blocker (queue_blocker_finish hb hc₁)⟩
      · exact ⟨_, queue_step_eq_some_of_blocker (queue_blocker_timeout hb h₂)⟩
      · exact ⟨_, queue_step_eq_some_of_blocker (queue_blocker_tick hb (lt_of_le_of_ne ha₁ h₂))⟩
    obtain ⟨s', hs'⟩ := hs
    exact ⟨_, by simp only [PolicyQueue.boundary, hs₁, hb, ↓reduceIte, hs']; rfl⟩
  · have hb' : s₁.busy = false := by simpa using hb
    by_cases hf : s₁.faulted = true
    · exact ⟨_, by
        simp only [PolicyQueue.boundary, hs₁, hb', hf, Bool.false_eq_true, ↓reduceIte]; rfl⟩
    · have hf' : s₁.faulted = false := by simpa using hf
      cases hq : s₁.requested with
      | nil =>
        exact ⟨_, by
          simp only [PolicyQueue.boundary, hs₁, hb', hf', Bool.false_eq_true, ↓reduceIte, hq]; rfl⟩
      | cons w rest =>
        have hs₂ := queue_step_eq_some_of_blocker (p := cfg.qsup)
          (queue_blocker_admit (by rw [hq]; exact List.cons_ne_nil w rest) hb' hf')
        exact ⟨_, by
          simp only [PolicyQueue.boundary, hs₁, hb', hf', Bool.false_eq_true, ↓reduceIte, hq, hs₂]
          rfl⟩

/-- **Under the queue supervisor's contract the program has a run on every stream.** For a queue
supervisor whose runs meet the contract `SupervisorQueue.Contract cfg.qsup`, the policy program
never blocks one of its own actions along its runs, so for every stream of requests `reqs` (each a
waypoint with a priority) and samples `smp` there are states and actions that are the program's own
output on it. This shows that the hypothesis `PolicyQueue.IsProgramRun` of
`cell_assured_program_measured_gain50_queue` can be met for every stream. A design statement, not
from MLS. -/
theorem _root_.RoboLean.Cell.PolicyQueue.exists_isProgramRun (cfg : PolicyQueue.Config)
    (hsup : SupervisorQueue.Contract cfg.qsup)
    (reqs : ℕ → List (Waypoint × SupervisorQueue.Priority)) (smp : ℕ → Policy.Sample) :
    ∃ (st : ℕ → PolicyQueue.State) (acts : ℕ → List SupervisorQueue.Action),
      PolicyQueue.IsProgramRun cfg reqs smp st acts := by
  let next : ℕ → PolicyQueue.State → List SupervisorQueue.Action × PolicyQueue.State :=
    fun k s => (PolicyQueue.boundary cfg k (reqs k) (smp k) s).getD ([], s)
  let st : ℕ → PolicyQueue.State := fun k =>
    Nat.rec (motive := fun _ => PolicyQueue.State) (PolicyQueue.State.init cfg)
      (fun j sj => (next j sj).2) k
  let acts : ℕ → List SupervisorQueue.Action := fun k => (next k (st k)).1
  have hnext : ∀ k, SupervisorQueue.run cfg.qsup (Supervisor.State.init cfg.qsup.home)
      (queueActsUpTo acts k) = some (st k).sup →
        PolicyQueue.boundary cfg k (reqs k) (smp k) (st k) = some (acts k, st (k + 1)) := by
    intro k hk
    obtain ⟨hc1, -, hc3, -, -, -⟩ := hsup _ _ hk
    have hc : (st k).sup.busy = true → (st k).sup.commanded ≠ [] := fun hb => by
      obtain ⟨w, -, hw⟩ := hc1 hb
      exact List.ne_nil_of_mem ((hw w).mpr rfl)
    obtain ⟨r, hr⟩ := queue_boundary_isSome (k := k) (reqs := reqs k) (smp := smp k) hc hc3
    show _ = some ((next k (st k)).1, (next k (st k)).2)
    simp only [next, hr, Option.getD_some]
  have key : ∀ k, SupervisorQueue.run cfg.qsup (Supervisor.State.init cfg.qsup.home)
      (queueActsUpTo acts k) = some (st k).sup := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [queueActsUpTo, queue_run_append, ih]
      exact (queue_boundary_spec (hnext k ih)).run_apply
  exact ⟨st, acts, rfl, fun k => hnext k (key k)⟩

/-! ### The assured cell on the queue supervisor -/

/-- The standing hypotheses of the loop on measured samples for the cell with the queue supervisor
(the cell's supervisor parameters and a queue of capacity `cap`), from a timed run on measured
samples within `εq` (rad) and `εv` (rad/s) of the true state, tracking of the last admitted move
and the tube at home at time 0, for any tracking predicate `follows` for which the move corollary
holds. Seconds, radians, radians per second. A design statement, not from MLS. -/
theorem cell_measured_hyps_queue {cap : ℕ} {h T δa va ω δ εq εv : ℝ} (hh : 0 < h) (hT : 0 < T)
    (hN : ⌈T / h⌉₊ ≤ 25) (hω : 0 ≤ ω) (hδa : δ + εq ≤ δa) (hva : 2 * ω * δ + εv ≤ va)
    {follows : Waypoint → Waypoint → ℝ → ℝ → Prop}
    {x v : ℝ → Fin 3 → ℝ} {xm vm : ℕ → Fin 3 → ℝ} {c : ℕ → CellState}
    {acts : ℕ → List SupervisorQueue.Action}
    (hrun : IsMeasuredQueueCellRun (openCellParams h T δa va)
      { toParams := Instances.params, capacity := cap } xm vm c acts)
    (hsamp : ∀ k : ℕ, ∀ i : Fin 3, |xm k i - x (k * h) i| ≤ εq ∧ |vm k i - v (k * h) i| ≤ εv)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * h) ((k + 1) * h),
      follows (c (k + 1)).src (c (k + 1)).goal ((c (k + 1)).start * h) t)
    (hmove : MoveCorollary (openCellParams h T δa va) (quinticMoveRef (n := 3) hT) δ ω follows
      x v)
    (h0 : InTube δ ω (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    MeasuredHyps (openCellParams h T δa va) (quinticMoveRef hT) δ ω εq εv Instances.params.home
      follows x v xm vm (fun k => (c k).toLoop) where
  period_pos := hh
  duration_pos := hT
  ceil_le_bound := hN
  rate_nonneg := hω
  radius_add_le_posTol := hδa
  speed_add_le_velTol := hva
  home_linked := home_linked_eq_true
  run := hrun.isMeasuredOpenRun rfl
  samples := hsamp
  tracks := htrack
  move := hmove
  init_tube := h0

/-- **The assured cell on measured samples with the queue supervisor.** As
`cell_assured_measured_right`, for the queue supervisor with the cell's parameters
`Instances.params` (instance cells, home `(0, -40, 30)` degrees, age bound 25) and a queue of
capacity `cap`, whose runs are assumed to meet the contract `SupervisorQueue.Contract` (`hsup`):
for the cell's arm `cellArm` under computed torque with the gains `ω² I`, `2ω I` (MLS eq. (4.49),
p. 191), let `0 < h`, `0 < T`, `⌈T/h⌉ ≤ 25`, `0 < ω`, `δ ≤ 1/20`, `δ + εq ≤ δ_a`,
`2 ω δ + εv ≤ v_a` (seconds, radians, radians per second). For every timed run `c` of the cell loop
with the queue supervisor on measured samples `(xm, vm)` (`hrun`: at each boundary requests
followed by the policy's action on the measured sample, each accepted by the queue supervisor),
the sample error bound (`hsamp`), the tracking hypothesis on each period with
`|(M(x)⁻¹ d)ᵢ| ≤ ω² δ` (`htrack`), `(x, v)` continuous on `[0, ∞)` (`hcont`) and the arm starting
in the tube around home at rest (`h0`): the supervisor's state before boundary `k` is
`SupervisorQueue.run` of the actions sent so far; every point of both links keeps `9/100` m from
every obstacle at every `t ≥ 0`; the supervisor never faults and its age stays below 25; a move
admitted at boundary `k₀` is busy until and finished at boundary `k₀ + ⌈T/h⌉`, with the arm at its
goal; at each finish the arm is in the tube around the goal at rest and the tool at the true
configuration is within `(73/50) δ` m of the goal's tool position. That every admitted move is
linked, and that a faulted supervisor admits nothing, is taken from `hsup` only. A design
statement, not from MLS. -/
theorem cell_assured_measured_right_queue {cap : ℕ} {h T δa va ω δ εq εv : ℝ} (hh : 0 < h)
    (hT : 0 < T) (hN : ⌈T / h⌉₊ ≤ 25) (hω : 0 < ω) (hδa : δ + εq ≤ δa)
    (hva : 2 * ω * δ + εv ≤ va) (hδ : δ ≤ 1 / 20)
    (hsup : SupervisorQueue.Contract { toParams := Instances.params, capacity := cap })
    {x v acc d : ℝ → Fin 3 → ℝ} {xm vm : ℕ → Fin 3 → ℝ} {c : ℕ → CellState}
    {acts : ℕ → List SupervisorQueue.Action}
    (hrun : IsMeasuredQueueCellRun (openCellParams h T δa va)
      { toParams := Instances.params, capacity := cap } xm vm c acts)
    (hsamp : ∀ k : ℕ, ∀ i : Fin 3, |xm k i - x (k * h) i| ≤ εq ∧ |vm k i - v (k * h) i| ≤ εv)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * h) ((k + 1) * h),
      CellArmFollowsAccelRightAt ω T δ x v acc d (DegPoint.toRad (c (k + 1)).src)
        (DegPoint.toRad (c (k + 1)).goal) ((c (k + 1)).start * h) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube δ ω (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ k, SupervisorQueue.run { toParams := Instances.params, capacity := cap }
      (State.init Instances.params.home) (queueActsUpTo acts k) = some (c k).sup) ∧
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (c k).sup.faulted = false ∧ (c k).sup.age < 25) ∧
    (∀ k₀, (c k₀).sup.busy = false → (c (k₀ + 1)).sup.busy = true →
      (c (k₀ + 1)).sup.commanded = [(c (k₀ + 1)).goal] ∧
      (∀ j, j < ⌈T / h⌉₊ → (c (k₀ + 1 + j)).sup.busy = true) ∧
      (c (k₀ + ⌈T / h⌉₊ + 1)).sup.busy = false ∧
      (c (k₀ + ⌈T / h⌉₊ + 1)).sup.current = (c (k₀ + 1)).goal) ∧
    (∀ k, (c k).sup.busy = true → (c (k + 1)).sup.busy = false →
      (c k).sup.commanded = [(c k).goal] ∧ (c (k + 1)).sup.current = (c k).goal ∧
      InTube δ ω (DegPoint.toRad (c k).goal) 0 (x (k * h)) (v (k * h)) ∧
      dist (sceneTool (x (k * h))) (sceneTool (DegPoint.toRad (c k).goal)) ≤ 73 / 50 * δ) := by
  have H := cell_measured_hyps_queue hh hT hN hω.le hδa hva hrun hsamp htrack
    (cellArm_moveCorollary_accel_right (openCellParams h T δa va) hT hω hcont) h0
  have hc := hrun.loopContract hsup (fun _ _ hab => hab)
  obtain ⟨hclear, hfault, hfin, htool, htube⟩ :=
    H.assured hc (openCellParams_certify h T δa va) hδ sceneTool_lipschitz
  refine ⟨hrun.run_eq_apply, hclear, hfault, fun k₀ hidle hbusy => ?_, fun k hbusy hidle => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hfin k₀ hidle hbusy
    exact ⟨hrun.commanded_eq_apply _ hbusy, h1, h2, h3⟩
  · obtain ⟨h1, h2⟩ := htube k hbusy hidle
    exact ⟨hrun.commanded_eq_apply _ hbusy, h1, h2, htool k hbusy hidle⟩

/-- The loop data of the gain-50 configuration on the queue supervisor: `h = 1/10` s, `T = 2` s,
position tolerance `degToRad 3` rad, speed tolerance `33/10` rad/s, as for
`Policy.designNominalGain50`. A design statement, not from MLS. -/
theorem designNominalGain50_queue_loop :
    PolicyQueue.designNominalGain50.toConfig.loop =
      openCellParams (1 / 10) 2 (degToRad 3) (33 / 10) :=
  designNominalGain50_loop

/-- **The assured cell at the gain 50 with every decision taken by the program on the queue
supervisor, on measured samples, with a bounded disturbance (a design statement, not from MLS; the
arm `cellArm` of MLS Example 4.3, p. 172, under computed torque of MLS eq. (4.49), p. 191).** For
every run of the policy program on the queue supervisor at the configuration
`PolicyQueue.designNominalGain50` (`hprog`: the states `st` and actions `acts` are the program's own
output on the requests `reqs`, each a waypoint with a priority, and the samples `smp`), and every
queue supervisor (the cell's parameters, capacity `8`) whose runs meet the contract
`SupervisorQueue.Contract` (`hsup`): if at every boundary `k/10` s each joint angle of the sample,
read in radians, is within `1/50` rad of the true joint angle and each joint speed estimate is
within `3/10` rad/s of the true joint speed (`hsamp`), and under `htrack` (on each period the arm
obeys its equations of motion `M ẍ + C ẋ + N = F + d` with the computed torque `F` at the gain `50`
rad/s tracking the quintic reference of the program's last admitted move, with right derivatives,
and `|(M(x)⁻¹ d)ᵢ| ≤ 75` rad/s² for every joint), `hcont` (`(x, v)` continuous on `[0, ∞)`) and
`h0` (the arm starts in the tube of radius `3/100` rad around home at rest): the links keep `9/100`
m from every obstacle at every `t ≥ 0`; the supervisor never faults and its age stays below 25; a
move admitted at boundary `k₀` keeps the supervisor busy at the boundaries `k₀ + 1, …, k₀ + 20` and
is finished at boundary `k₀ + 20` with the arm at its goal; and at each finish the tool is within
`219/5000` m of the goal's tool position. The conclusions are those of
`cell_assured_program_measured_gain50`. Proved from `cell_assured_measured_right_queue` with
`δ_a = 3` degrees, `v_a = 33/10` rad/s (`2 · 50 · 3/100 + 3/10`), `εq = 1/50` rad and
`εv = 3/10` rad/s. -/
theorem cell_assured_program_measured_gain50_queue
    (hsup : SupervisorQueue.Contract PolicyQueue.designNominalGain50.qsup)
    {reqs : ℕ → List (Waypoint × SupervisorQueue.Priority)} {smp : ℕ → Policy.Sample}
    {st : ℕ → PolicyQueue.State} {acts : ℕ → List SupervisorQueue.Action}
    (hprog : PolicyQueue.IsProgramRun PolicyQueue.designNominalGain50 reqs smp st acts)
    {x v acc d : ℝ → Fin 3 → ℝ}
    (hsamp : ∀ k : ℕ, ∀ i : Fin 3,
      |(smp k).toRad PolicyQueue.designNominalGain50.toConfig i - x (k * (1 / 10)) i| ≤ 1 / 50 ∧
        |(smp k).velRad i - v (k * (1 / 10)) i| ≤ 3 / 10)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelRightAt 50 2 (3 / 100) x v acc d (DegPoint.toRad (st (k + 1)).src)
        (DegPoint.toRad (st (k + 1)).goal) ((st (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 50 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (st k).sup.faulted = false ∧ (st k).sup.age < 25) ∧
    (∀ k₀, (st k₀).sup.busy = false → (st (k₀ + 1)).sup.busy = true →
      (∀ j, j < 20 → (st (k₀ + 1 + j)).sup.busy = true) ∧
      (st (k₀ + 20 + 1)).sup.busy = false ∧ (st (k₀ + 20 + 1)).sup.current = (st (k₀ + 1)).goal) ∧
    (∀ k, (st k).sup.busy = true → (st (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (st k).goal)) ≤
        219 / 5000) := by
  have hrun : IsMeasuredQueueCellRun (openCellParams (1 / 10) 2 (degToRad 3) (33 / 10))
      { toParams := Instances.params, capacity := 8 }
      (fun k => (smp k).toRad PolicyQueue.designNominalGain50.toConfig) (fun k => (smp k).velRad)
      (fun k => (st k).toCell) acts := by
    have h := hprog.isMeasuredCellRun
    rw [designNominalGain50_queue_loop] at h
    exact h
  have hδa : (3 : ℝ) / 100 + 1 / 50 ≤ degToRad 3 := by
    have := Real.pi_gt_three
    unfold degToRad
    push_cast
    linarith
  obtain ⟨-, hclear, hfault, hfin, htool⟩ :=
    cell_assured_measured_right_queue (ω := 50) (δ := 3 / 100) (εq := 1 / 50) (εv := 3 / 10)
      (by norm_num) (by norm_num) (by rw [design_steps]; norm_num) (by norm_num) hδa
      (by norm_num) (by norm_num) hsup hrun hsamp htrack hcont h0
  refine ⟨hclear, hfault, fun k₀ hidle hbusy => ?_, fun k hbusy hidle => ?_⟩
  · obtain ⟨-, h1, h2, h3⟩ := hfin k₀ hidle hbusy
    rw [design_steps] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · obtain ⟨-, -, -, h4⟩ := htool k hbusy hidle
    exact le_of_le_of_eq h4 (by norm_num)

/-- **The assured cell at the gain 50 with every decision taken by the program on the queue
supervisor, on exact samples, with a bounded disturbance.** As
`cell_assured_program_measured_gain50_queue`, with the samples read in radians and rad/s equal to
the true state at every boundary `k/10` s (`hexact`) in place of `hsamp` (an exact sample is within
every nonnegative error). A design statement, not from MLS (computed torque of MLS eq. (4.49),
p. 191). -/
theorem cell_assured_program_measured_gain50_queue_exact
    (hsup : SupervisorQueue.Contract PolicyQueue.designNominalGain50.qsup)
    {reqs : ℕ → List (Waypoint × SupervisorQueue.Priority)} {smp : ℕ → Policy.Sample}
    {st : ℕ → PolicyQueue.State} {acts : ℕ → List SupervisorQueue.Action}
    (hprog : PolicyQueue.IsProgramRun PolicyQueue.designNominalGain50 reqs smp st acts)
    {x v acc d : ℝ → Fin 3 → ℝ}
    (hexact : ∀ k : ℕ, x (k * (1 / 10)) = (smp k).toRad PolicyQueue.designNominalGain50.toConfig ∧
      v (k * (1 / 10)) = (smp k).velRad)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelRightAt 50 2 (3 / 100) x v acc d (DegPoint.toRad (st (k + 1)).src)
        (DegPoint.toRad (st (k + 1)).goal) ((st (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 50 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (st k).sup.faulted = false ∧ (st k).sup.age < 25) ∧
    (∀ k₀, (st k₀).sup.busy = false → (st (k₀ + 1)).sup.busy = true →
      (∀ j, j < 20 → (st (k₀ + 1 + j)).sup.busy = true) ∧
      (st (k₀ + 20 + 1)).sup.busy = false ∧ (st (k₀ + 20 + 1)).sup.current = (st (k₀ + 1)).goal) ∧
    (∀ k, (st k).sup.busy = true → (st (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (st k).goal)) ≤
        219 / 5000) :=
  cell_assured_program_measured_gain50_queue hsup hprog (fun k i => by
    rw [(hexact k).1, (hexact k).2, sub_self, sub_self, abs_zero]; norm_num) htrack hcont h0

end RoboLean.Cell.Loop
