import RoboLean.Cell.PolicyRun
import RoboLean.Cell.AssuredMeasured

/-!
# The assured cell with the program's run as its hypothesis

The assured cell theorems of `RoboLean.Cell.AssuredContract` (exact samples) and
`RoboLean.Cell.AssuredMeasured` (measured samples) at the design point, with the hypothesis on the
run replaced by: the supervisor's states and actions are the policy program's own output
(`Policy.IsProgramRun`) on a stream of requests and samples. Every decision of the loop — the due
test, the arrival test, finish, tick, timeout, the order of requests, rejections and admissions —
is then taken by the program `Policy.boundary`, which applies the supervisor's `step` to each
action; the timed run of the cell loop that the earlier theorems assume is derived from it
(`Policy.IsProgramRun.isCellRun`, `Policy.IsProgramRun.isMeasuredCellRun`).

* `Policy.design`: the program's configuration at the design point (the cell's supervisor
  parameters, `h = 1/10` s, `T = 2` s, position tolerance `7/4` degrees, speed tolerance `5`
  rad/s, encoders of `2^18` counts per revolution).
* `cell_assured_program_design`: the conclusions of `cell_assured_contract_design_tight_right` for
  every run of the program whose samples are the true state.
* `cell_assured_program_measured_design`: the same for every run of the program whose samples are
  within `1/2000` rad and `1/5` rad/s of the true state.
* `Policy.exists_isProgramRun`: under the supervisor's contract the program never blocks one of
  its own actions, so it has a run on every stream of requests and samples.

The supervisor's contract `Supervisor.Contract Instances.params` stays a premise; it is proved in
the Veil project from the conditions Veil's SMT solver discharges. These are design statements,
not from MLS. The arm is `cellArm` (MLS Example 4.3, printed p. 172) under computed torque (MLS
eq. (4.49), p. 191), with right derivatives only; the statements concern the ideal rigid-body
model with a bounded disturbance and the sampled loop with a bounded sample error, not a physical
arm, and the compiled program only through the Lean definitions it is built from.
-/

namespace RoboLean.Cell.Policy

/-- The policy program's configuration at the design point: the cell's supervisor parameters
`Instances.params` (three cells, home `(0, -40, 30)` degrees, age bound 25), the period `1/10` s,
the move duration `2` s, the position tolerance `7/4` degrees (`7π/720 ≈ 0.0305` rad), the speed
tolerance `5` rad/s and encoders of `2^18` counts per revolution. A design definition, not from
MLS. -/
def design : Config where
  sup := Supervisor.Instances.params
  period := 1 / 10
  duration := 2
  posTol := 7 / 4
  velTol := 5
  countsPerRev := 2 ^ 18

end RoboLean.Cell.Policy

noncomputable section

namespace RoboLean.Cell.Loop

open Set Supervisor

/-- The loop data of the design configuration: `h = 1/10` s, `T = 2` s, position tolerance
`degToRad (7/4)` rad, speed tolerance `5` rad/s. A design statement, not from MLS. -/
theorem design_loop :
    Policy.design.loop = openCellParams (1 / 10) 2 (degToRad (7 / 4)) 5 := by
  show openCellParams (((1 / 10 : ℚ)) : ℝ) ((2 : ℚ) : ℝ) (degToRad (7 / 4)) ((5 : ℚ) : ℝ) = _
  norm_num

/-- **A run of the program is a measured timed run of the cell loop.** The cell states of the
program's states and the program's actions form a timed run of the cell loop on the program's own
samples, read in radians and rad/s; nothing is assumed about the true state. A design statement,
not from MLS. -/
theorem _root_.RoboLean.Cell.Policy.IsProgramRun.isMeasuredCellRun {cfg : Policy.Config}
    {reqs : ℕ → List Waypoint}
    {smp : ℕ → Policy.Sample} {st : ℕ → Policy.State} {acts : ℕ → List Action}
    (h : Policy.IsProgramRun cfg reqs smp st acts) :
    IsMeasuredCellRun cfg.loop cfg.sup (fun k => (smp k).toRad cfg) (fun k => (smp k).velRad)
      (fun k => (st k).toCell) acts :=
  ⟨by show (st 0).toCell = _; rw [h.1]; rfl, fun k => boundary_spec (h.2 k)⟩

/-- **The assured cell with every decision taken by the program, on exact samples.** For the
cell's arm under computed torque with `ω = 80` rad/s and the tube radius `δ = 3/100` rad, and for
every run of the policy program at the design configuration `Policy.design` (`hprog`: the states
`st` and actions `acts` are the program's own output on the requests `reqs` and the samples
`smp`), whose samples read in radians and rad/s are the true state at every boundary `k/10` s
(`hexact`), and for every supervisor whose runs meet the contract (`hsup`): under the hypotheses
`htrack` (on each period the arm obeys its equations of motion with the computed torque tracking
the quintic reference of the program's last admitted move, with right derivatives, and
`|(M(x)⁻¹ d)ᵢ| ≤ 192` rad/s²), `hcont` and `h0` of `cell_assured_contract_design_tight_right`:
the links keep `9/100` m from every obstacle at every `t ≥ 0`; the supervisor never faults and its
age stays below 25; a move admitted at boundary `k₀` is finished at boundary `k₀ + 20` with the arm
at its goal; and at each finish the tool is within `219/5000` m of the goal's tool position.
Proved from `cell_assured_contract_right` with the arrival tolerances `7/4` degrees and `5` rad/s.
A design statement, not from MLS. -/
theorem cell_assured_program_design (hsup : Supervisor.Contract Instances.params)
    {reqs : ℕ → List Waypoint} {smp : ℕ → Policy.Sample} {st : ℕ → Policy.State}
    {acts : ℕ → List Action} (hprog : Policy.IsProgramRun Policy.design reqs smp st acts)
    {x v acc d : ℝ → Fin 3 → ℝ}
    (hexact : ∀ k : ℕ, x (k * (1 / 10)) = (smp k).toRad Policy.design ∧
      v (k * (1 / 10)) = (smp k).velRad)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelRightAt 80 2 (3 / 100) x v acc d (DegPoint.toRad (st (k + 1)).src)
        (DegPoint.toRad (st (k + 1)).goal) ((st (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 80 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (st k).sup.faulted = false ∧ (st k).sup.age < 25) ∧
    (∀ k₀, (st k₀).sup.busy = false → (st (k₀ + 1)).sup.busy = true →
      (st (k₀ + 20 + 1)).sup.busy = false ∧ (st (k₀ + 20 + 1)).sup.current = (st (k₀ + 1)).goal) ∧
    (∀ k, (st k).sup.busy = true → (st (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (st k).goal)) ≤
        219 / 5000) := by
  have hp : ((Policy.design.period : ℚ) : ℝ) = 1 / 10 := by
    show (((1 / 10 : ℚ)) : ℝ) = 1 / 10
    norm_num
  have hrun : IsCellRun (openCellParams (1 / 10) 2 (degToRad (7 / 4)) 5) Instances.params x v
      (fun k => (st k).toCell) acts := by
    have h := hprog.isCellRun (x := x) (v := v) (fun k => by rw [hp]; exact hexact k)
    rw [design_loop] at h
    exact h
  have hδa : (3 : ℝ) / 100 ≤ degToRad (7 / 4) :=
    le_trans (by norm_num) design_radius_add_le_posTol
  obtain ⟨-, hclear, hfault, hfin, htool⟩ :=
    cell_assured_contract_right (h := 1 / 10) (T := 2) (δa := degToRad (7 / 4)) (va := 5)
      (ω := 80) (δ := 3 / 100) (by norm_num) (by norm_num) (by rw [design_steps]; norm_num)
      (by norm_num) hδa (by norm_num) (by norm_num) hsup hrun htrack hcont h0
  refine ⟨hclear, hfault, fun k₀ hidle hbusy => ?_, fun k hbusy hidle => ?_⟩
  · obtain ⟨-, -, h2, h3⟩ := hfin k₀ hidle hbusy
    rw [design_steps] at h2 h3
    exact ⟨h2, h3⟩
  · obtain ⟨-, -, -, h4⟩ := htool k hbusy hidle
    exact le_of_le_of_eq h4 (by norm_num)

/-- **The assured cell with every decision taken by the program, on measured samples.** As
`cell_assured_program_design`, with the samples no longer equal to the true state: at every
boundary `k/10` s each joint angle of the sample, read in radians, is within `1/2000` rad of the
true joint angle and each joint speed estimate is within `1/5` rad/s of the true joint speed
(`hsamp`). The conclusions are unchanged and concern the true motion. Proved from
`cell_assured_measured_design_right`. A design statement, not from MLS. -/
theorem cell_assured_program_measured_design (hsup : Supervisor.Contract Instances.params)
    {reqs : ℕ → List Waypoint} {smp : ℕ → Policy.Sample} {st : ℕ → Policy.State}
    {acts : ℕ → List Action} (hprog : Policy.IsProgramRun Policy.design reqs smp st acts)
    {x v acc d : ℝ → Fin 3 → ℝ}
    (hsamp : ∀ k : ℕ, ∀ i : Fin 3, |(smp k).toRad Policy.design i - x (k * (1 / 10)) i| ≤ 1 / 2000 ∧
      |(smp k).velRad i - v (k * (1 / 10)) i| ≤ 1 / 5)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelRightAt 80 2 (3 / 100) x v acc d (DegPoint.toRad (st (k + 1)).src)
        (DegPoint.toRad (st (k + 1)).goal) ((st (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 80 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (st k).sup.faulted = false ∧ (st k).sup.age < 25) ∧
    (∀ k₀, (st k₀).sup.busy = false → (st (k₀ + 1)).sup.busy = true →
      (st (k₀ + 20 + 1)).sup.busy = false ∧ (st (k₀ + 20 + 1)).sup.current = (st (k₀ + 1)).goal) ∧
    (∀ k, (st k).sup.busy = true → (st (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (st k).goal)) ≤
        219 / 5000) := by
  have hrun : IsMeasuredCellRun (openCellParams (1 / 10) 2 (degToRad (7 / 4)) 5) Instances.params
      (fun k => (smp k).toRad Policy.design) (fun k => (smp k).velRad) (fun k => (st k).toCell)
      acts := by
    have h := hprog.isMeasuredCellRun
    rw [design_loop] at h
    exact h
  exact cell_assured_measured_design_right hsup hrun hsamp htrack hcont h0

/-! ### The program never blocks one of its own actions -/

/-- An action whose guards all hold (`Action.blocker` returns `none`) is accepted by `step`, with
its effect `State.apply`. A design statement, not from MLS. -/
theorem step_eq_some_of_blocker {p : Supervisor.Params} {s : Supervisor.State} {a : Action}
    (h : a.blocker p s = none) : step p s a = some (s.apply a) := by
  unfold step
  rw [h]

/-- `finish` is accepted by a busy supervisor with a commanded waypoint. A design statement, not
from MLS. -/
theorem blocker_finish {p : Supervisor.Params} {s : Supervisor.State} (hb : s.busy = true)
    (hc : s.commanded ≠ []) : Action.finish.blocker p s = none := by
  show (if s.busy = false then some "not-busy"
    else if s.commanded.isEmpty then some "no-command" else none) = none
  simp [hb, List.isEmpty_iff, hc]

/-- `tick` is accepted by a busy supervisor whose age is below the bound. A design statement, not
from MLS. -/
theorem blocker_tick {p : Supervisor.Params} {s : Supervisor.State} (hb : s.busy = true)
    (ha : s.age < p.bound) : Action.tick.blocker p s = none := by
  show (if s.busy = false then some "not-busy"
    else if s.age < p.bound then none else some "age-at-bound") = none
  simp [hb, ha]

/-- `timeout` is accepted by a busy supervisor whose age is the bound. A design statement, not
from MLS. -/
theorem blocker_timeout {p : Supervisor.Params} {s : Supervisor.State} (hb : s.busy = true)
    (ha : s.age = p.bound) : Action.timeout.blocker p s = none := by
  show (if s.busy = false then some "not-busy"
    else if s.age = p.bound then none else some "age-not-at-bound") = none
  simp [hb, ha]

/-- `reject w` is accepted when `w` is requested and not linked to the waypoint the arm is at. A
design statement, not from MLS. -/
theorem blocker_reject {p : Supervisor.Params} {s : Supervisor.State} {w : Waypoint}
    (hw : w ∈ s.requested) (hl : linked p.cells s.current w = false) :
    (Action.reject w).blocker p s = none := by
  show (if w ∉ s.requested then some "not-requested"
    else if linked p.cells s.current w = true then some "linked" else none) = none
  simp [hw, hl]

/-- `admit w` is accepted when `w` is requested, the supervisor is idle and not faulted, and `w` is
linked to the waypoint the arm is at. A design statement, not from MLS. -/
theorem blocker_admit {p : Supervisor.Params} {s : Supervisor.State} {w : Waypoint}
    (hw : w ∈ s.requested) (hb : s.busy = false) (hf : s.faulted = false)
    (hl : linked p.cells s.current w = true) : (Action.admit w).blocker p s = none := by
  show (if w ∉ s.requested then some "not-requested"
    else if s.busy = true then some "not-idle"
    else if s.faulted = true then some "faulted"
    else if linked p.cells s.current w = false then some "not-linked" else none) = none
  simp [hw, hb, hf, hl]

/-- The idle policy's forwarding and rejecting never blocks: on every queue it returns a result,
leaves the supervisor's `busy`, `faulted` and `current` unchanged, and the waypoint it chooses to
admit is requested and linked to the waypoint the arm is at. A design statement, not from MLS. -/
theorem admitNext_isSome (p : Supervisor.Params) :
    ∀ (q : List Waypoint) (s : Supervisor.State), ∃ pre s₁ adm rest,
      Policy.admitNext p s q = some (pre, s₁, adm, rest) ∧ s₁.busy = s.busy ∧
        s₁.faulted = s.faulted ∧ s₁.current = s.current ∧
        ∀ w, adm = some w → w ∈ s₁.requested ∧ linked p.cells s₁.current w = true := by
  intro q
  induction q with
  | nil =>
    intro s
    exact ⟨[], s, none, [], rfl, rfl, rfl, rfl, fun _ h => absurd h (by simp)⟩
  | cons w q ih =>
    intro s
    have hreq : step p s (.request w) = some (s.apply (.request w)) :=
      step_eq_some_of_blocker rfl
    have hmem : w ∈ (s.apply (.request w)).requested := List.mem_insert_self
    by_cases hl : linked p.cells s.current w = true
    · refine ⟨[.request w], s.apply (.request w), some w, q, ?_, rfl, rfl, rfl, ?_⟩
      · simp only [Policy.admitNext, hl, ↓reduceIte, hreq]
      · intro w' h
        obtain rfl := (Option.some.inj h).symm
        exact ⟨hmem, hl⟩
    · have hl' : linked p.cells (s.apply (.request w)).current w = false := by
        show linked p.cells s.current w = false
        simpa using hl
      have hrej : step p (s.apply (.request w)) (.reject w) =
          some ((s.apply (.request w)).apply (.reject w)) :=
        step_eq_some_of_blocker (blocker_reject hmem hl')
      obtain ⟨pre, s₃, adm, rest, h, hb, hf, hc, hadm⟩ :=
        ih ((s.apply (.request w)).apply (.reject w))
      refine ⟨.request w :: .reject w :: pre, s₃, adm, rest, ?_, hb, hf, hc, hadm⟩
      simp only [Policy.admitNext, hl, Bool.false_eq_true, ↓reduceIte, hreq, hrej, h]

/-- **The program never blocks one of its own actions.** From a state whose supervisor has a
commanded waypoint while busy and an age at most the bound (two clauses of the supervisor's
contract), the policy program returns a result at every boundary, for every request list and
every sample. A design statement, not from MLS. -/
theorem boundary_isSome {cfg : Policy.Config} {k : ℕ} {reqs : List Waypoint}
    {smp : Policy.Sample} {st : Policy.State}
    (hc : st.sup.busy = true → st.sup.commanded ≠ []) (ha : st.sup.age ≤ cfg.sup.bound) :
    ∃ r, Policy.boundary cfg k reqs smp st = some r := by
  by_cases hb : st.sup.busy = true
  · have hs : ∃ s', step cfg.sup st.sup (Policy.busyAction cfg k st smp) = some s' := by
      unfold Policy.busyAction
      split_ifs with h1 h2
      · exact ⟨_, step_eq_some_of_blocker (blocker_finish hb (hc hb))⟩
      · exact ⟨_, step_eq_some_of_blocker (blocker_timeout hb h2)⟩
      · exact ⟨_, step_eq_some_of_blocker (blocker_tick hb (lt_of_le_of_ne ha h2))⟩
    obtain ⟨s', hs'⟩ := hs
    exact ⟨_, by simp only [Policy.boundary, hb, ↓reduceIte, hs']; rfl⟩
  · have hb' : st.sup.busy = false := by simpa using hb
    by_cases hf : st.sup.faulted = true
    · exact ⟨_, by simp only [Policy.boundary, hb', hf, Bool.false_eq_true, ↓reduceIte]; rfl⟩
    · have hf' : st.sup.faulted = false := by simpa using hf
      obtain ⟨pre, s₁, adm, rest, h, h1, h2, -, hadm⟩ :=
        admitNext_isSome cfg.sup (st.pending ++ reqs) st.sup
      cases adm with
      | none =>
        exact ⟨_, by simp only [Policy.boundary, hb', hf', Bool.false_eq_true, ↓reduceIte, h]; rfl⟩
      | some w =>
        obtain ⟨hw, hl⟩ := hadm w rfl
        have hs₂ := step_eq_some_of_blocker (blocker_admit hw (h1.trans hb') (h2.trans hf') hl)
        exact ⟨_, by
          simp only [Policy.boundary, hb', hf', Bool.false_eq_true, ↓reduceIte, h, hs₂]; rfl⟩

/-- **Under the supervisor's contract the program has a run on every stream.** For a supervisor
whose runs meet the contract, the policy program never blocks one of its own actions along its
runs, so for every stream of requests `reqs` and samples `smp` there are states and actions that
are the program's own output on it. This shows that the hypothesis `Policy.IsProgramRun` of
`cell_assured_program_design` and `cell_assured_program_measured_design` can be met for every
stream. A design statement, not from MLS. -/
theorem _root_.RoboLean.Cell.Policy.exists_isProgramRun (cfg : Policy.Config)
    (hsup : Supervisor.Contract cfg.sup) (reqs : ℕ → List Waypoint)
    (smp : ℕ → Policy.Sample) :
    ∃ (st : ℕ → Policy.State) (acts : ℕ → List Action),
      Policy.IsProgramRun cfg reqs smp st acts := by
  let next : ℕ → Policy.State → List Action × Policy.State := fun k s =>
    (Policy.boundary cfg k (reqs k) (smp k) s).getD ([], s)
  let st : ℕ → Policy.State := fun k =>
    Nat.rec (motive := fun _ => Policy.State) (Policy.State.init cfg) (fun j sj => (next j sj).2) k
  let acts : ℕ → List Action := fun k => (next k (st k)).1
  have hnext : ∀ k, run cfg.sup (Supervisor.State.init cfg.sup.home) (actsUpTo acts k) =
      some (st k).sup →
        Policy.boundary cfg k (reqs k) (smp k) (st k) = some (acts k, st (k + 1)) := by
    intro k hk
    obtain ⟨hc1, -, hc3, -, -, -⟩ := hsup _ _ hk
    have hc : (st k).sup.busy = true → (st k).sup.commanded ≠ [] := fun hb => by
      obtain ⟨w, -, hw⟩ := hc1 hb
      exact List.ne_nil_of_mem ((hw w).mpr rfl)
    obtain ⟨r, hr⟩ := boundary_isSome (k := k) (reqs := reqs k) (smp := smp k) hc hc3
    show _ = some ((next k (st k)).1, (next k (st k)).2)
    simp only [next, hr, Option.getD_some]
  have key : ∀ k, run cfg.sup (Supervisor.State.init cfg.sup.home) (actsUpTo acts k) =
      some (st k).sup := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [actsUpTo, run_append_apply, ih]
      exact (boundary_spec (hnext k ih)).run_apply
  exact ⟨st, acts, rfl, fun k => hnext k (key k)⟩

end RoboLean.Cell.Loop
