import RoboLean.Cell.LoopOpen
import RoboLean.Cell.SupervisorContract
import RoboLean.Cell.AssuredInstanceRight

/-!
# The assured cell with the supervisor's contract as its premise

The assured cell theorem of `RoboLean.Cell.AssuredInstanceRight` with the supervisor's part
delegated: the theorems here take the supervisor's contract `Supervisor.Contract` at the cell's
parameters as a premise, and every fact about which moves the supervisor admits comes from it.
The contract is proved for every parameter value in the Veil project, from the verification
conditions of the Veil model of the supervisor, which Veil's SMT solver discharges with proof
reconstruction.

The loop data `openCellParams` link two waypoints when the program's link test on the instance
cells returns `true`. A timed run of the cell loop (`IsCellRun`: queue actions, then the policy's
action, each accepted by the supervisor) is mapped to a run of the open loop of
`RoboLean.Cell.LoopOpen`, whose admissions carry no guard, using only what an accepted action does
to the supervisor's state (`step_eq_apply`), never when it is accepted. The contract applied to the
supervisor's state at each boundary, the result of `Supervisor.run` on the actions sent so far,
gives the loop-level contract: a busy supervisor's move is linked by the link test, and a faulted
supervisor is idle. A `true` link test on the instance cells means that a cell of the scene
contains both waypoints (`sceneLinked_of_linked_eq_true`), which certifies the clearance.

* `cell_assured_contract_right`: the statement of `cell_assured_accel_right` with the premise
  `Supervisor.Contract Instances.params` and the loop data `openCellParams`.
* `cell_assured_contract_design_tight_right`: at `h = 1/10` s, `T = 2` s, `ω = 80` rad/s,
  `δ = δ_a = 3/100` rad and `v_a = 24/5` rad/s.
* `cell_contract_clauses`: the contract's six clauses at the supervisor's state before every
  boundary.

The arm is `cellArm` (MLS Example 4.3, printed p. 172, with the cell's parameters) under computed
torque (MLS eq. (4.49), p. 191), with the position and the velocity required to have right
derivatives only. These are design statements, not from MLS. They concern the ideal rigid-body
model with a bounded disturbance and the ideal sampled loop; they do not assert that a closed-loop
solution exists, and say nothing about sensing, delay, actuator limits or a physical arm.
-/

noncomputable section

namespace RoboLean.Cell.Loop

open Set Supervisor

/-- The loop data of the cell for the period `h` (s), the move duration `T` (s) and the arrival
tolerances `δ_a` (rad), `v_a` (rad/s), with the program's link test as the link relation:
waypoints in rational degrees mapped to radians by `DegPoint.toRad`, two waypoints linked when
`Supervisor.linked` on the instance cells returns `true`, and the supervisor's age bound 25. A
design definition, not from MLS. -/
def openCellParams (h T δa va : ℝ) : Params 3 Waypoint where
  pos := DegPoint.toRad
  linked a b := Supervisor.linked Instances.params.cells a b = true
  period := h
  duration := T
  posTol := δa
  velTol := va
  bound := Instances.params.bound

/-- An accepted step of the executable supervisor is the action's effect `State.apply`; nothing is
said about when the step is accepted. A design statement, not from MLS. -/
theorem step_eq_apply {p : Supervisor.Params} {s s' : Supervisor.State} {a : Action}
    (h : step p s a = some s') : s' = s.apply a := by
  unfold step at h
  split at h
  · simp at h
  · exact (Option.some.inj h).symm

/-- `Supervisor.run` on a nonempty list takes the first step and runs the rest from its result,
read off the definition. A design statement, not from MLS. -/
theorem run_cons_apply (p : Supervisor.Params) (s : Supervisor.State) (a : Action)
    (l : List Action) : run p s (a :: l) = (step p s a).bind fun s' => run p s' l := by
  cases h : step p s a with
  | none =>
    show (match step p s a with | none => none | some s' => run p s' l) = none
    rw [h]
  | some s' =>
    show (match step p s a with | none => none | some s' => run p s' l) = run p s' l
    rw [h]

/-- Running a concatenation of action lists runs the first and then the second, from the
definition of `Supervisor.run`. A design statement, not from MLS. -/
theorem run_append_apply (p : Supervisor.Params) (s : Supervisor.State) (l₁ l₂ : List Action) :
    run p s (l₁ ++ l₂) = (run p s l₁).bind fun s' => run p s' l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons a l ih =>
    rw [List.cons_append, run_cons_apply, run_cons_apply]
    cases step p s a with
    | none => rfl
    | some s' => exact ih s'

/-- A single accepted action runs to its result. A design statement, not from MLS. -/
theorem run_singleton_of_step {p : Supervisor.Params} {s s' : Supervisor.State} {a : Action}
    (h : step p s a = some s') : run p s [a] = some s' := by
  rw [run_cons_apply, h]
  rfl

/-- The policy's actions are accepted by the supervisor and run to the next state. A design
statement, not from MLS. -/
theorem PolicyStep.run_apply {L : Loop.Params 3 Waypoint} {p : Supervisor.Params} {k : ℕ}
    {θ θ' : Fin 3 → ℝ} {c c' : CellState} {pol : List Action}
    (h : PolicyStep L p k θ θ' c pol c') : Supervisor.run p c.sup pol = some c'.sup := by
  cases h with
  | finish _ _ _ _ hstep => exact run_singleton_of_step hstep
  | timeout _ _ _ _ hstep => exact run_singleton_of_step hstep
  | tick _ _ _ _ hstep => exact run_singleton_of_step hstep
  | wait => rfl
  | admit _ _ _ hstep => exact run_singleton_of_step hstep

/-- The actions of a boundary run the supervisor's state to the next one. A design statement, not
from MLS. -/
theorem Boundary.run_apply {L : Loop.Params 3 Waypoint} {p : Supervisor.Params} {k : ℕ}
    {θ θ' : Fin 3 → ℝ} {c c' : CellState} {acts : List Action}
    (h : Boundary L p k θ θ' c acts c') : Supervisor.run p c.sup acts = some c'.sup := by
  obtain ⟨pre, pol, s₁, rfl, -, hpre, hpol⟩ := h
  rw [run_append_apply, hpre]
  exact hpol.run_apply

/-- **The executable supervisor's state is the result of `run`.** Along a timed run of the cell
loop, the supervisor's state before boundary `k` is `Supervisor.run p (State.init p.home)` of all
the actions sent before `k`. A design statement, not from MLS. -/
theorem IsCellRun.run_eq_apply {L : Loop.Params 3 Waypoint} {p : Supervisor.Params}
    {x v : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (h : IsCellRun L p x v c acts) (k : ℕ) :
    run p (Supervisor.State.init p.home) (actsUpTo acts k) = some (c k).sup := by
  induction k with
  | zero => rw [h.1]; rfl
  | succ k ih =>
    rw [actsUpTo, run_append_apply, ih]
    exact (h.2 k).run_apply

/-- Queue actions accepted by the supervisor change neither `busy`, `faulted`, `age`, `current`
nor the commanded list, by their effects alone. A design statement, not from MLS. -/
theorem run_queue_apply {p : Supervisor.Params} {s s₁ : Supervisor.State} {pre : List Action}
    (hq : ∀ a ∈ pre, IsQueueAction a) (h : run p s pre = some s₁) :
    s₁.busy = s.busy ∧ s₁.faulted = s.faulted ∧ s₁.age = s.age ∧ s₁.current = s.current ∧
      s₁.commanded = s.commanded := by
  induction pre generalizing s with
  | nil =>
    have h' : some s = some s₁ := h
    obtain rfl := Option.some.inj h'
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons a l ih =>
    rw [run_cons_apply] at h
    cases h₂ : step p s a with
    | none =>
      rw [h₂] at h
      exact absurd h (by simp)
    | some s₂ =>
      rw [h₂] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih (fun b hb => hq b (List.mem_cons_of_mem a hb)) h
      have ha := hq a List.mem_cons_self
      obtain rfl := step_eq_apply h₂
      cases a <;> simp [IsQueueAction] at ha <;> exact ⟨h1, h2, h3, h4, h5⟩

/-- One boundary keeps the controller's goal as the commanded list while busy, by the effects of
the accepted actions. A design statement, not from MLS. -/
theorem Boundary.commanded_eq_apply {L : Loop.Params 3 Waypoint} {p : Supervisor.Params} {k : ℕ}
    {θ θ' : Fin 3 → ℝ} {c c' : CellState} {acts : List Action}
    (h : Boundary L p k θ θ' c acts c')
    (hc : c.sup.busy = true → c.sup.commanded = [c.goal]) :
    c'.sup.busy = true → c'.sup.commanded = [c'.goal] := by
  obtain ⟨pre, pol, s₁, -, hq, hpre, hpol⟩ := h
  obtain ⟨h1, -, -, -, h5⟩ := run_queue_apply hq hpre
  cases hpol with
  | finish s' _ _ _ hstep =>
    obtain rfl := step_eq_apply hstep
    simp [Supervisor.State.apply]
  | timeout s' _ _ _ hstep =>
    obtain rfl := step_eq_apply hstep
    simp [Supervisor.State.apply]
  | tick s' hbusy _ _ hstep =>
    obtain rfl := step_eq_apply hstep
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
    obtain rfl := step_eq_apply hstep
    intro _
    simp [Supervisor.State.apply]

/-- Along a timed run of the cell loop, the commanded list is the controller's goal while busy, by
the effects of the accepted actions. A design statement, not from MLS. -/
theorem IsCellRun.commanded_eq_apply {L : Loop.Params 3 Waypoint} {p : Supervisor.Params}
    {x v : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (h : IsCellRun L p x v c acts) (k : ℕ) :
    (c k).sup.busy = true → (c k).sup.commanded = [(c k).goal] := by
  induction k with
  | zero => rw [h.1]; simp [CellState.init, Supervisor.State.init]
  | succ k ih => exact (h.2 k).commanded_eq_apply ih

/-- **One boundary of the cell loop is a step of the open loop.** If the loop data's bound is the
supervisor's and the commanded list is the goal while busy, the loop states of a boundary are
related by `OpenStep`; only the effects of the accepted actions are used. A design statement, not
from MLS. -/
theorem Boundary.toOpenStep {L : Loop.Params 3 Waypoint} {p : Supervisor.Params}
    (hbound : L.bound = p.bound) {k : ℕ} {θ θ' : Fin 3 → ℝ} {c c' : CellState}
    {acts : List Action} (h : Boundary L p k θ θ' c acts c')
    (hc : c.sup.busy = true → c.sup.commanded = [c.goal]) :
    OpenStep L k θ θ' c.toLoop c'.toLoop := by
  obtain ⟨pre, pol, s₁, -, hq, hpre, hpol⟩ := h
  obtain ⟨h1, h2, h3, h4, h5⟩ := run_queue_apply hq hpre
  have hloop : ({ c with sup := s₁ } : CellState).toLoop = c.toLoop := by
    simp [CellState.toLoop, h1, h2, h3, h4]
  rw [← hloop]
  cases hpol with
  | finish s' hbusy hdue harr hstep =>
    obtain rfl := step_eq_apply hstep
    have hcom : s₁.commanded = [c.goal] := h5 ▸ hc (h1 ▸ hbusy)
    have e : ({ c with sup := s₁.apply .finish } : CellState).toLoop =
        { ({ c with sup := s₁ } : CellState).toLoop with
          current := ({ c with sup := s₁ } : CellState).toLoop.goal, busy := false, age := 0 } := by
      simp [CellState.toLoop, Supervisor.State.apply, hcom]
    rw [e]
    exact OpenStep.finish _ hbusy hdue harr
  | timeout s' hbusy hnot hage hstep =>
    obtain rfl := step_eq_apply hstep
    have e : ({ c with sup := s₁.apply .timeout } : CellState).toLoop =
        { ({ c with sup := s₁ } : CellState).toLoop with
          busy := false, faulted := true, age := 0 } := by
      simp [CellState.toLoop, Supervisor.State.apply]
    rw [e]
    exact OpenStep.timeout _ hbusy hnot (by rw [hbound]; exact hage)
  | tick s' hbusy hnot hage hstep =>
    obtain rfl := step_eq_apply hstep
    have e : ({ c with sup := s₁.apply .tick } : CellState).toLoop =
        { ({ c with sup := s₁ } : CellState).toLoop with
          age := ({ c with sup := s₁ } : CellState).toLoop.age + 1 } := by
      simp [CellState.toLoop, Supervisor.State.apply]
    rw [e]
    exact OpenStep.tick _ hbusy hnot (by rw [hbound]; exact hage)
  | wait hidle => exact OpenStep.wait _ hidle
  | admit w s' hidle hstep =>
    obtain rfl := step_eq_apply hstep
    convert OpenStep.admit ({ c with sup := s₁ } : CellState).toLoop w hidle using 1
    simp [CellState.toLoop, Supervisor.State.apply]

/-- **A timed run of the cell loop is a run of the open loop.** For loop data whose bound is the
supervisor's, the loop states of a timed run of the cell loop form a timed run of the open loop
from `p.home`; no guard of the supervisor is used. A design statement, not from MLS. -/
theorem IsCellRun.isOpenRun {L : Loop.Params 3 Waypoint} {p : Supervisor.Params}
    (hbound : L.bound = p.bound) {x v : ℝ → Fin 3 → ℝ} {c : ℕ → CellState}
    {acts : ℕ → List Action} (h : IsCellRun L p x v c acts) :
    IsOpenRun L p.home x v (fun k => (c k).toLoop) :=
  ⟨by show (c 0).toLoop = _; rw [h.1]; rfl,
    fun k => (h.2 k).toOpenStep hbound (h.commanded_eq_apply k)⟩

/-- **The supervisor's contract gives the loop-level contract.** Along a timed run of the cell
loop, the supervisor's state before boundary `k` is `Supervisor.run` of the actions sent so far;
the contract's sixth clause links every commanded waypoint, in particular the goal of a busy
loop, to the waypoint the arm is at, and its fifth clause makes a faulted supervisor idle. For
loop data whose link relation contains the program's link test, the loop states meet
`LoopContract`. A design statement, not from MLS. -/
theorem IsCellRun.loopContract {L : Loop.Params 3 Waypoint} {p : Supervisor.Params}
    (hsup : Supervisor.Contract p)
    (hlink : ∀ a b, Supervisor.linked p.cells a b = true → L.linked a b)
    {x v : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (h : IsCellRun L p x v c acts) : LoopContract L (fun k => (c k).toLoop) := fun k => by
  obtain ⟨-, -, -, -, h5, h6⟩ := hsup _ _ (h.run_eq_apply k)
  refine ⟨fun hb => hlink _ _ (h6 _ ?_), h5⟩
  rw [h.commanded_eq_apply k hb]
  exact List.mem_singleton_self _

/-- A supervisor box built from a scene box contains a waypoint, by the executable test, only if
the scene box contains it. A design statement, not from MLS. -/
theorem DegBox.contains_of_toSupervisorBox {B : DegBox} {w : Waypoint}
    (h : B.toSupervisorBox.contains w = true) : B.Contains w := by
  simp only [Supervisor.Box.contains, DegBox.toSupervisorBox, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3, of_decide_eq_true h4,
    of_decide_eq_true h5, of_decide_eq_true h6⟩

/-- **The meaning of a `true` link test.** If the program's link test on the instance cells
returns `true` for two waypoints, some cell of the scene contains both. This interprets the link
relation that the contract speaks of; it says nothing about which actions the supervisor accepts.
A design statement, not from MLS. -/
theorem sceneLinked_of_linked_eq_true {a b : Waypoint}
    (h : Supervisor.linked Instances.params.cells a b = true) : SceneLinked a b := by
  unfold Supervisor.linked at h
  rw [List.any_eq_true] at h
  obtain ⟨c, hc, hab⟩ := h
  rw [Bool.and_eq_true] at hab
  have hmem : c ∈ sceneCells.map DegBox.toSupervisorBox := hc
  obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hmem
  exact ⟨B, hB, DegBox.contains_of_toSupervisorBox hab.1, DegBox.contains_of_toSupervisorBox hab.2⟩

/-- The scene's cells certify the loop data `openCellParams` at the inflation `1/20` rad for the
clearance `sceneClear`. A design statement, not from MLS. -/
theorem openCellParams_certify (h T δa va : ℝ) :
    CellsCertify (openCellParams h T δa va) cellInflation sceneClear :=
  sceneCells_certify _ (fun _ => rfl) fun _ _ hab => sceneLinked_of_linked_eq_true hab

/-- The link test links the home waypoint `(0, -40, 30)` degrees to itself: the crossing cell
contains it. A check of the data by evaluation, not a statement about the supervisor's decisions.
A design statement, not from MLS. -/
theorem home_linked_eq_true :
    Supervisor.linked Instances.params.cells Instances.params.home Instances.params.home =
      true := by
  decide +kernel

/-- The standing hypotheses of the open loop for the cell, from a timed run of the executable
supervisor, tracking of the last admitted move and the tube at home at time 0, for any tracking
predicate `follows` for which the move corollary holds. A design statement, not from MLS. -/
theorem cell_open_hyps {h T δa va ω δ : ℝ} (hh : 0 < h) (hT : 0 < T) (hN : ⌈T / h⌉₊ ≤ 25)
    (hω : 0 ≤ ω) (hδa : δ ≤ δa) (hva : 2 * ω * δ ≤ va)
    {follows : Waypoint → Waypoint → ℝ → ℝ → Prop}
    {x v : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsCellRun (openCellParams h T δa va) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * h) ((k + 1) * h),
      follows (c (k + 1)).src (c (k + 1)).goal ((c (k + 1)).start * h) t)
    (hmove : MoveCorollary (openCellParams h T δa va) (quinticMoveRef (n := 3) hT) δ ω follows
      x v)
    (h0 : InTube δ ω (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    OpenHyps (openCellParams h T δa va) (quinticMoveRef hT) δ ω Instances.params.home follows x v
      (fun k => (c k).toLoop) where
  period_pos := hh
  duration_pos := hT
  ceil_le_bound := hN
  rate_nonneg := hω
  radius_le_posTol := hδa
  speed_le_velTol := hva
  home_linked := home_linked_eq_true
  run := hrun.isOpenRun rfl
  tracks := htrack
  move := hmove
  init_tube := h0

/-- **The assured cell with the supervisor's contract as its premise.** For the cell's arm
`cellArm` under computed torque with the gains `ω² I`, `2ω I` (MLS eq. (4.49), p. 191, along a
motion as on p. 301), the scene's three cells and obstacles, and the executable cell supervisor
with its instance cells and age bound 25, whose runs are assumed to meet the contract
`Supervisor.Contract Instances.params` (`hsup`): let `0 < h`, `0 < T`, `⌈T/h⌉ ≤ 25`, `0 < ω`,
`δ ≤ min δ_a (1/20)`, `2 ω δ ≤ v_a` (seconds, radians, radians per second). Then for every timed
run `c` of the cell loop with the actions `acts` sent to the supervisor and every motion
`(x, v, acc)` with disturbance torque `d`, under the hypotheses
* (harness, `hrun`) at each boundary `k h` the actions sent are queue actions followed by the
  policy's action on the exact sample `(x (k h), v (k h))`, each accepted by the supervisor;
* (harness and plant, `htrack`) at every instant `t` of each period `(k h, (k + 1) h]` the arm
  obeys its equations of motion `M ẍ + C ẋ + N = F + d` with the computed torque `F` tracking the
  quintic reference of the last admitted move, `x` and `v` have the right derivatives `v t` and
  `acc t` (within `[t, ∞)`, so the acceleration may jump), and `|(M(x)⁻¹ d)ᵢ| ≤ ω² δ` for every
  joint;
* (plant, `hcont`) `(x, v)` is continuous on `[0, ∞)`;
* (harness, `h0`) the arm starts in the tube around home at rest,
the conclusions are those of `cell_assured_accel_right`: the supervisor's state before boundary
`k` is `Supervisor.run` of the actions sent so far, so the contract's clauses hold of it
(`cell_contract_clauses`); every point of both links keeps a Euclidean distance of at least
`9/100` m from every obstacle at every `t ≥ 0`; the supervisor never faults and its age stays below
25; a move admitted at boundary `k₀` (commanded waypoint `goal`) is busy until and finished at
boundary `k₀ + ⌈T/h⌉`, with the arm at `goal`; at each finish the arm is in the tube around the
goal at rest and the tool is within `(73/50) δ` m of the goal's tool position. That every admitted
move is linked, and that a faulted supervisor admits nothing, is taken from `hsup` only. A design
statement, not from MLS. -/
theorem cell_assured_contract_right {h T δa va ω δ : ℝ} (hh : 0 < h) (hT : 0 < T)
    (hN : ⌈T / h⌉₊ ≤ 25) (hω : 0 < ω) (hδa : δ ≤ δa) (hva : 2 * ω * δ ≤ va) (hδ : δ ≤ 1 / 20)
    (hsup : Supervisor.Contract Instances.params)
    {x v acc d : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsCellRun (openCellParams h T δa va) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * h) ((k + 1) * h),
      CellArmFollowsAccelRightAt ω T δ x v acc d (DegPoint.toRad (c (k + 1)).src)
        (DegPoint.toRad (c (k + 1)).goal) ((c (k + 1)).start * h) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube δ ω (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ k, run Instances.params (State.init Instances.params.home) (actsUpTo acts k) =
      some (c k).sup) ∧
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
  have H := cell_open_hyps hh hT hN hω.le hδa hva hrun htrack
    (cellArm_moveCorollary_accel_right (openCellParams h T δa va) hT hω hcont) h0
  have hc := hrun.loopContract hsup (fun _ _ hab => hab)
  obtain ⟨hclear, hfault, hfin, htool, htube⟩ :=
    H.assured hc (openCellParams_certify h T δa va) hδ sceneTool_lipschitz
  refine ⟨hrun.run_eq_apply, hclear, hfault, fun k₀ hidle hbusy => ?_, fun k hbusy hidle => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hfin k₀ hidle hbusy
    exact ⟨hrun.commanded_eq_apply _ hbusy, h1, h2, h3⟩
  · obtain ⟨h1, h2⟩ := htube k hbusy hidle
    exact ⟨hrun.commanded_eq_apply _ hbusy, h1, h2, htool k hbusy hidle⟩

/-- **The assured cell at the tube radius `3/100` rad with the supervisor's contract as its
premise.** With `h = 1/10` s, `T = 2` s, `ω = 80` rad/s, `δ = δ_a = 3/100` rad and
`v_a = 24/5` rad/s, and `|(M(x)⁻¹ d)ᵢ| ≤ 192` rad/s² for every joint, with the position and the
velocity required to have right derivatives only (`CellArmFollowsAccelRightAt`), for every run of
the supervisor that meets the contract `Supervisor.Contract Instances.params` (`hsup`): the links
keep `9/100` m from every obstacle at every `t ≥ 0`, the supervisor never faults and its age stays
below 25, a move admitted at boundary `k₀` is finished at boundary `k₀ + 20`, and at each finish
the tool is within `219/5000` m of the goal's tool position. The other hypotheses are those of
`cell_assured_contract_right`: about the harness, that at each boundary the actions sent are queue
actions followed by the policy's action on the exact sample, each accepted by the supervisor
(`hrun`), and that the arm starts in the tube around home at rest (`h0`); about the harness and
the plant, that on each period the arm obeys its equations of motion with the computed torque
tracking the quintic reference of the last admitted move, with the acceleration from the right,
and the disturbance bound above (`htrack`); about the plant, that `(x, v)` is continuous on
`[0, ∞)` (`hcont`). A design statement, not from MLS. -/
theorem cell_assured_contract_design_tight_right (hsup : Supervisor.Contract Instances.params)
    {x v acc d : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsCellRun (openCellParams (1 / 10) 2 (3 / 100) (24 / 5)) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelRightAt 80 2 (3 / 100) x v acc d (DegPoint.toRad (c (k + 1)).src)
        (DegPoint.toRad (c (k + 1)).goal) ((c (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 80 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (c k).sup.faulted = false ∧ (c k).sup.age < 25) ∧
    (∀ k₀, (c k₀).sup.busy = false → (c (k₀ + 1)).sup.busy = true →
      (c (k₀ + 20 + 1)).sup.busy = false ∧ (c (k₀ + 20 + 1)).sup.current = (c (k₀ + 1)).goal) ∧
    (∀ k, (c k).sup.busy = true → (c (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (c k).goal)) ≤
        219 / 5000) := by
  obtain ⟨-, hclear, hfault, hfin, htool⟩ :=
    cell_assured_contract_right (by norm_num) (by norm_num) (by rw [design_steps]; norm_num)
      (by norm_num) le_rfl (by norm_num) (by norm_num) hsup hrun htrack hcont h0
  refine ⟨hclear, hfault, fun k₀ hidle hbusy => ?_, fun k hbusy hidle => ?_⟩
  · obtain ⟨-, -, h2, h3⟩ := hfin k₀ hidle hbusy
    rw [design_steps] at h2 h3
    exact ⟨h2, h3⟩
  · obtain ⟨-, -, -, h4⟩ := htool k hbusy hidle
    linarith

/-- **The contract's clauses at every boundary.** Along a timed run of the cell loop, for a
supervisor whose runs meet the contract, the supervisor's state before every boundary satisfies
the contract's six clauses: it is `Supervisor.run` of the actions sent so far. A design statement,
not from MLS; waypoints in rational degrees, the age in ticks. -/
theorem cell_contract_clauses (hsup : Supervisor.Contract Instances.params)
    {L : Loop.Params 3 Waypoint} {x v : ℝ → Fin 3 → ℝ} {c : ℕ → CellState}
    {acts : ℕ → List Action} (hrun : IsCellRun L Instances.params x v c acts) (k : ℕ) :
    ((c k).sup.busy = true → ∃ w, linked Instances.params.cells (c k).sup.current w = true ∧
        ∀ u, u ∈ (c k).sup.commanded ↔ u = w) ∧
      ((c k).sup.busy = false → ∀ u, u ∉ (c k).sup.commanded) ∧
      (c k).sup.age ≤ Instances.params.bound ∧
      ((c k).sup.busy = false → (c k).sup.age = 0) ∧
      ((c k).sup.faulted = true → (c k).sup.busy = false) ∧
      (∀ u, u ∈ (c k).sup.commanded → linked Instances.params.cells (c k).sup.current u = true) :=
  hsup _ _ (hrun.run_eq_apply k)

end RoboLean.Cell.Loop
