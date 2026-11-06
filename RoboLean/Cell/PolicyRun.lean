import RoboLean.Cell.Policy
import RoboLean.Cell.AssuredContract

/-!
# The program's runs are timed runs of the cell loop

The policy program `RoboLean.Cell.Policy.boundary` decides at each period boundary from exact
rationals: the sample's encoder counts read as degrees, its speed estimates in rad/s, the move's
admission boundary, the period and the duration. This file reads the program's data in the units
of the loop model and proves that every output of the program is a boundary step of the cell loop
(`Boundary`, from `RoboLean.Cell.LoopSupervisor`), so that the states and actions the program
produces on any stream of requests and samples are a timed run of the cell loop (`IsCellRun`)
when the samples are the true state.

* `Policy.State.toCell`, `Policy.Sample.toRad`, `Policy.Sample.velRad`, `Policy.Config.loop`: the
  program's state, sample and configuration in the loop model's terms (radians, rad/s, seconds).
* `due_eq_true_iff`, `arrived_eq_true_iff`: the program's time and arrival tests decide the loop
  model's `Due` and `Arrived` exactly.
* `boundary_spec`: every output of `Policy.boundary` is a `Boundary` step.
* `Policy.IsProgramRun.isCellRun`: a run of the program on samples equal to the true state at every
  boundary is a timed run of the cell loop.

The proofs unfold the program and use only the effects of the accepted actions (`step_eq_apply`)
and the reading of `Supervisor.run` on a list (`run_cons_apply`); nothing about the supervisor's
guards beyond the program's own test results is used. A design statement, not from MLS. Units:
degrees for waypoints and for the program's position tolerance, radians and rad/s in the loop
model, seconds for the period and the duration.
-/

noncomputable section

namespace RoboLean.Cell.Policy

open RoboLean.Cell.Supervisor RoboLean.Cell.Loop

/-- The cell loop state of a policy state: the supervisor's state and the controller's record of
the last admitted move; the request queue is forgotten. A design model, not from MLS. -/
def State.toCell (st : State) : CellState :=
  ⟨st.sup, st.src, st.goal, st.start⟩

/-- The joint angles of a sample in radians: the encoder counts read in degrees at the
configuration's resolution (`Sample.angle`), then converted by `DegPoint.toRad`. A design
convention, not from MLS. -/
def Sample.toRad (cfg : Config) (s : Sample) : Fin 3 → ℝ :=
  DegPoint.toRad (s.angle cfg)

/-- The joint speed estimates of a sample as a real vector, in radians per second. A design
convention, not from MLS. -/
def Sample.velRad (s : Sample) : Fin 3 → ℝ :=
  ![(s.vel.1 : ℝ), (s.vel.2.1 : ℝ), (s.vel.2.2 : ℝ)]

/-- The loop data of a configuration: the cell's loop data `openCellParams` with the period and
the duration in seconds, the position tolerance converted from degrees to radians and the speed
tolerance in rad/s. The link relation and the bound are the cell's (`openCellParams`); the
boundary step reads neither. A design definition, not from MLS. -/
def Config.loop (cfg : Config) : Loop.Params 3 Waypoint :=
  openCellParams (cfg.period : ℝ) (cfg.duration : ℝ) (degToRad cfg.posTol) (cfg.velTol : ℝ)

end RoboLean.Cell.Policy

namespace RoboLean.Cell.Loop

open Set Supervisor

/-- **The program's time test is the loop model's.** `Policy.due` decides over `ℚ` exactly the
real inequality `start · h + T ≤ k · h` of `Due` (seconds). A design statement, not from MLS. -/
theorem due_eq_true_iff {cfg : Policy.Config} {st : Policy.State} {k : ℕ} :
    Policy.due cfg st k = true ↔ Due cfg.loop st.toCell.toLoop k := by
  unfold Policy.due Due
  rw [decide_eq_true_iff]
  show _ ↔ ((st.start : ℕ) : ℝ) * ((cfg.period : ℚ) : ℝ) + ((cfg.duration : ℚ) : ℝ) ≤
    ((k : ℕ) : ℝ) * ((cfg.period : ℚ) : ℝ)
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- The program's test `absLe a t` decides `|a| ≤ t`, read in `ℝ`. A design statement, not from
MLS. -/
theorem absLe_eq_true_iff (a t : ℚ) : Policy.absLe a t = true ↔ |(a : ℝ)| ≤ (t : ℝ) := by
  unfold Policy.absLe
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by exact_mod_cast h1⟩
    have : ((-a : ℚ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast h2
    push_cast at this
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨by exact_mod_cast h2, ?_⟩
    have : -(a : ℝ) ≤ (t : ℝ) := by linarith
    exact_mod_cast this

/-- In radians, two angles given in degrees differ by at most a tolerance given in degrees exactly
when they do in degrees: `|a π/180 − g π/180| ≤ t π/180 ↔ |a − g| ≤ t`. A design statement, not
from MLS. -/
theorem abs_degToRad_sub_le_iff (a g t : ℚ) :
    |degToRad a - degToRad g| ≤ degToRad t ↔ |((a - g : ℚ) : ℝ)| ≤ (t : ℝ) := by
  have hc : (0 : ℝ) < Real.pi / 180 := by positivity
  have e1 : degToRad a - degToRad g = ((a - g : ℚ) : ℝ) * (Real.pi / 180) := by
    unfold degToRad; push_cast; ring
  have e2 : degToRad t = (t : ℝ) * (Real.pi / 180) := by
    unfold degToRad; ring
  rw [e1, e2, abs_mul, abs_of_pos hc]
  exact mul_le_mul_iff_of_pos_right hc

/-- **The program's arrival test is the loop model's.** `Policy.arrived` on a sample decides
exactly `Arrived` for the sample read in radians and rad/s, the goal in radians and the
tolerances `degToRad posTol` (rad) and `velTol` (rad/s). A design statement, not from MLS. -/
theorem arrived_eq_true_iff {cfg : Policy.Config} {g : Waypoint} {s : Policy.Sample} :
    Policy.arrived cfg g s = true ↔ Arrived cfg.loop g (s.toRad cfg) s.velRad := by
  unfold Policy.arrived Arrived
  simp only [Bool.and_eq_true, absLe_eq_true_iff]
  rw [Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_one]
  simp only [Policy.Sample.toRad, Policy.Sample.velRad, Policy.Config.loop, openCellParams,
    DegPoint.toRad, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one,
    Matrix.cons_val_one, abs_degToRad_sub_le_iff]
  tauto

/-- The idle policy's queue actions are forwardings and rejections, and the supervisor runs them
to the state the policy reports. A design statement, not from MLS. -/
theorem admitNext_spec {p : Supervisor.Params} {s s₁ : Supervisor.State} {q : List Waypoint}
    {pre : List Action} {adm : Option Waypoint} {rest : List Waypoint}
    (h : Policy.admitNext p s q = some (pre, s₁, adm, rest)) :
    (∀ a ∈ pre, IsQueueAction a) ∧ run p s pre = some s₁ := by
  induction q generalizing s pre adm rest with
  | nil =>
    simp only [Policy.admitNext, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -, -⟩ := h
    exact ⟨fun _ h => absurd h List.not_mem_nil, rfl⟩
  | cons w q ih =>
    unfold Policy.admitNext at h
    split at h
    · split at h
      · exact absurd h (by simp)
      · rename_i s₂ hs₂
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -, -⟩ := h
        refine ⟨fun a ha => ?_, run_singleton_of_step hs₂⟩
        rw [List.mem_singleton] at ha
        subst ha
        trivial
    · split at h
      · exact absurd h (by simp)
      · rename_i s₂ hs₂
        split at h
        · exact absurd h (by simp)
        · rename_i s₃ hs₃
          split at h
          · exact absurd h (by simp)
          · rename_i pre' s₄ adm' rest' hrec
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, -, -⟩ := h
            obtain ⟨hq, hrun⟩ := ih hrec
            refine ⟨fun a ha => ?_, ?_⟩
            · rcases List.mem_cons.mp ha with rfl | ha
              · trivial
              rcases List.mem_cons.mp ha with rfl | ha
              · trivial
              exact hq a ha
            · rw [run_cons_apply, hs₂]
              show run p s₂ (Action.reject w :: pre') = some s₄
              rw [run_cons_apply, hs₃]
              exact hrun

/-- **Every output of the program is a boundary step of the cell loop.** If the policy program
at boundary `k`, with the requests `reqs` and the sample `smp`, takes the state `st` to `st'` with
the actions `acts`, then `acts` and the cell states of `st` and `st'` form a `Boundary` step of
the cell loop for the loop data `cfg.loop`, the supervisor's parameters `cfg.sup` and the sample
read in radians and rad/s. A design statement, not from MLS. -/
theorem boundary_spec {cfg : Policy.Config} {k : ℕ} {reqs : List Waypoint} {smp : Policy.Sample}
    {st st' : Policy.State} {acts : List Action}
    (h : Policy.boundary cfg k reqs smp st = some (acts, st')) :
    Boundary cfg.loop cfg.sup k (smp.toRad cfg) smp.velRad st.toCell acts st'.toCell := by
  unfold Policy.boundary at h
  split at h
  · -- busy: one action of the busy branch
    rename_i hbusy
    split at h
    · exact absurd h (by simp)
    · rename_i s' hs'
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨[], [Policy.busyAction cfg k st smp], st.sup, rfl, fun a ha => absurd ha
        List.not_mem_nil, rfl, ?_⟩
      have hc : ({ st.toCell with sup := st.sup } : CellState) = st.toCell := rfl
      have hc' : ({ st with sup := s', pending := st.pending ++ reqs } : Policy.State).toCell =
          { st.toCell with sup := s' } := rfl
      rw [hc, hc']
      unfold Policy.busyAction at hs' ⊢
      by_cases hfin : (Policy.due cfg st k && Policy.arrived cfg st.goal smp) = true
      · simp only [hfin, ↓reduceIte] at hs' ⊢
        rw [Bool.and_eq_true] at hfin
        exact PolicyStep.finish _ s' hbusy (due_eq_true_iff.mp hfin.1)
          (arrived_eq_true_iff.mp hfin.2) hs'
      · have hnot : ¬ (Due cfg.loop st.toCell.toLoop k ∧
            Arrived cfg.loop st.toCell.goal (smp.toRad cfg) smp.velRad) := by
          rintro ⟨h1, h2⟩
          exact hfin (by rw [Bool.and_eq_true]; exact ⟨due_eq_true_iff.mpr h1,
            arrived_eq_true_iff.mpr h2⟩)
        simp only [hfin, Bool.false_eq_true, ↓reduceIte] at hs' ⊢
        by_cases hage : st.sup.age = cfg.sup.bound
        · simp only [hage, ↓reduceIte] at hs' ⊢
          exact PolicyStep.timeout _ s' hbusy hnot hage hs'
        · simp only [hage, ↓reduceIte] at hs' ⊢
          exact PolicyStep.tick _ s' hbusy hnot hage hs'
  · rename_i hidle
    have hidle' : st.sup.busy = false := by simpa using hidle
    split at h
    · -- idle and faulted: nothing
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], [], st.sup, rfl, fun a ha => absurd ha List.not_mem_nil, rfl,
        PolicyStep.wait _ hidle'⟩
    · -- idle and not faulted: forward, reject, admit
      split at h
      · exact absurd h (by simp)
      · rename_i pre s₁ rest hnext
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hq, hrun⟩ := admitNext_spec hnext
        obtain ⟨h1, -, -, -, -⟩ := run_queue_apply hq hrun
        refine ⟨pre, [], s₁, (List.append_nil pre).symm, hq, hrun, ?_⟩
        exact PolicyStep.wait _ (by rw [h1]; exact hidle')
      · rename_i pre s₁ w rest hnext
        split at h
        · exact absurd h (by simp)
        · rename_i s₂ hs₂
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hq, hrun⟩ := admitNext_spec hnext
          obtain ⟨h1, -, -, -, -⟩ := run_queue_apply hq hrun
          refine ⟨pre, [.admit w], s₁, rfl, hq, hrun, ?_⟩
          exact PolicyStep.admit _ w s₂ (by rw [h1]; exact hidle') hs₂

/-- **A run of the program is a timed run of the cell loop.** If the states `st` and the actions
`acts` are the program's own output on the requests `reqs` and the samples `smp`
(`Policy.IsProgramRun`), and at every boundary `k h` the sample read in radians and rad/s is the
true state `(x (k h), v (k h))`, then the cell states of `st` and the actions `acts` form a timed
run of the cell loop for the loop data `cfg.loop` and the supervisor's parameters `cfg.sup`. A
design statement, not from MLS. -/
theorem _root_.RoboLean.Cell.Policy.IsProgramRun.isCellRun {cfg : Policy.Config}
    {reqs : ℕ → List Waypoint}
    {smp : ℕ → Policy.Sample} {st : ℕ → Policy.State} {acts : ℕ → List Action}
    (h : Policy.IsProgramRun cfg reqs smp st acts) {x v : ℝ → Fin 3 → ℝ}
    (hx : ∀ k : ℕ, x (k * (cfg.period : ℝ)) = (smp k).toRad cfg ∧
      v (k * (cfg.period : ℝ)) = (smp k).velRad) :
    IsCellRun cfg.loop cfg.sup x v (fun k => (st k).toCell) acts := by
  refine ⟨by show (st 0).toCell = _; rw [h.1]; rfl, fun k => ?_⟩
  have hb := boundary_spec (h.2 k)
  show Boundary cfg.loop cfg.sup k (x (k * (cfg.period : ℝ))) (v (k * (cfg.period : ℝ)))
    (st k).toCell (acts k) (st (k + 1)).toCell
  rw [(hx k).1, (hx k).2]
  exact hb

end RoboLean.Cell.Loop
