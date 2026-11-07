import RoboLean.Cell.PolicyQueueRun
import RoboLean.Cell.SupervisorQueueContractHand
import RoboLean.Cell.SupervisorContractHand
import RoboLean.Cell.AssuredProgramInstance
import RoboLean.Cell.AssuredInstanceTight

/-!
# The program-form theorems at the gain 50 hold for a moving run

A satisfying instance of `cell_assured_program_measured_gain50_queue` (the policy program on the
queue supervisor) and of `cell_assured_program_measured_gain50` (the policy program on the
request-set supervisor), both at the gain-50 design point: period `1/10` s, move duration `2` s,
arrival tolerances `3` degrees and `33/10` rad/s, encoders of `2^18` counts per revolution.

The demonstration move goes from home `(0, -40, 30)` to the waypoint above the pick slot
`(50, -35, 30)` (degrees). One normal request arrives at boundary 0; the program admits it at
boundary 0, ticks at the boundaries 1 to 19, finishes at boundary 20 and is idle afterwards. The arm
follows the quintic reference of the move exactly, with zero disturbance (`demoMotion`, `demoVel`,
`demoAcc`, `d = 0`), and the program reads the encoder samples `encoderSample demoMotion demoVel`
(each joint angle to the nearest of `2^18` counts per revolution, each joint speed floored to a
multiple of `1/5` rad/s).

* `demoQueue_isProgramRun`, `demoSet_isProgramRun`: the states and actions of the move are the
  program's own output on that request and those samples, on the queue supervisor and on the
  request-set supervisor.
* `cell_assured_program_measured_gain50_queue_hyps_demo`,
  `cell_assured_program_measured_gain50_hyps_demo`: the run meets every hypothesis of the two
  theorems other than the supervisor's contract.
* `program_queue_demo_gain50_assured`, `program_demo_gain50_assured`: the conclusions of the two
  theorems for this run, with the contracts discharged by
  `SupervisorQueue.contract_of_queue_invariant` and `Supervisor.contract_of_design`.

Design statements, not from MLS (the arm is `cellArm`, MLS Example 4.3, printed p. 172, under
computed torque, MLS eq. (4.49), p. 191). Seconds, radians, radians per second; waypoints in
rational degrees. The motion is the exact tracking of the reference with zero disturbance, so the
run shows that the hypotheses hold together for a moving arm; it says nothing about the
disturbances a real arm meets, about real encoders or speed estimators, or about a physical arm.
-/

noncomputable section

namespace RoboLean.Cell.Loop

open Set Supervisor

/-- The samples the program reads in the demonstration run: at boundary `k` (time `k/10` s), the
encoder sample `encoderSample` of the demonstration motion (joint angles to the nearest of `2^18`
counts per revolution, joint speeds in rad/s floored to a multiple of `1/5`). A design definition,
not from MLS. -/
def demoSamples : ℕ → Policy.Sample := encoderSample demoMotion demoVel

/-- The requests of the demonstration run on the queue supervisor: the waypoint above the pick slot
`(50, -35, 30)` (degrees) with normal priority at boundary 0, nothing afterwards. A design
definition, not from MLS. -/
def demoQueueReqs (k : ℕ) : List (Waypoint × SupervisorQueue.Priority) :=
  if k = 0 then [(Instances.liftPick, .normal)] else []

/-- The states of the program on the queue supervisor in the demonstration run: the initial state
before boundary 0, busy with age `k - 1` on the move from home `(0, -40, 30)` to `(50, -35, 30)`
(degrees, admitted at boundary 0) before the boundaries `1, …, 20`, idle at the goal from boundary
21 on. A design definition, not from MLS. -/
def demoQueueState (k : ℕ) : PolicyQueue.State :=
  if k = 0 then PolicyQueue.State.init PolicyQueue.designNominalGain50
  else if k ≤ 20 then ⟨demoBusy (k - 1), Instances.params.home, Instances.liftPick, 0⟩
  else ⟨demoDone, Instances.params.home, Instances.liftPick, 0⟩

/-- The actions the program sends to the queue supervisor in the demonstration run: the normal
request and `admit` at boundary 0, `tick` at `1, …, 19`, `finish` at 20, nothing afterwards. A
design definition, not from MLS. -/
def demoQueueActs (k : ℕ) : List SupervisorQueue.Action :=
  if k = 0 then [.request Instances.liftPick .normal, .admit]
  else if k < 20 then [.tick] else if k = 20 then [.finish] else []

/-- The demonstration samples are within the gain-50 design's sample error: at every boundary `k`
and joint `i`, the angle read in radians at the configuration `Policy.designNominalGain50` is within
`1/50` rad of `demoMotion (k/10) i` and the speed estimate within `3/10` rad/s of
`demoVel (k/10) i` (from `encoderSample_within`: `1/2000` rad and `1/5` rad/s). A design statement,
not from MLS. -/
theorem demoSamples_within (k : ℕ) (i : Fin 3) :
    |(demoSamples k).toRad Policy.designNominalGain50 i - demoMotion (k * (1 / 10)) i| ≤ 1 / 50 ∧
      |(demoSamples k).velRad i - demoVel (k * (1 / 10)) i| ≤ 3 / 10 := by
  obtain ⟨h1, h2⟩ := encoderSample_within demoMotion demoVel k i
  exact ⟨h1.trans (by norm_num), h2.trans (by norm_num)⟩

/-- At boundary 20 (time `2` s) the demonstration sample passes the arrival test of the gain-50
configuration for the goal `(50, -35, 30)` (degrees): the true state is the goal at rest, the angles
read are within `1/2000` rad of it, below `3` degrees, and the speeds within `1/5` rad/s of zero,
below `33/10` rad/s. A design statement, not from MLS. -/
theorem demoSamples_arrived :
    Policy.arrived Policy.designNominalGain50 Instances.liftPick (demoSamples 20) = true := by
  rw [arrived_eq_true_iff, designNominalGain50_loop]
  intro i
  have h2 : (0 : ℝ) + 2 ≤ ((20 : ℕ) : ℝ) * (1 / 10) := by norm_num
  obtain ⟨h1, h1'⟩ := encoderSample_within demoMotion demoVel 20 i
  have hx : demoMotion (((20 : ℕ) : ℝ) * (1 / 10)) = DegPoint.toRad Instances.liftPick :=
    moveRef_of_ge (by norm_num : (0 : ℝ) < 2) h2
  have hv : demoVel (((20 : ℕ) : ℝ) * (1 / 10)) = 0 :=
    moveRefDeriv_of_ge (by norm_num : (0 : ℝ) < 2) h2
  rw [hx] at h1
  rw [hv, Pi.zero_apply, sub_zero] at h1'
  have hpi := Real.pi_gt_three
  have h3 : (1 : ℝ) / 2000 ≤ degToRad 3 := by
    unfold degToRad; push_cast; linarith
  exact ⟨h1.trans h3, h1'.trans (by show (1 : ℝ) / 5 ≤ 33 / 10; norm_num)⟩

/-- After every boundary the controller's record in the queue run is the move from home to the
waypoint above the pick slot admitted at boundary 0. A design statement, not from MLS. -/
theorem demoQueueState_succ_move (k : ℕ) :
    (demoQueueState (k + 1)).src = Instances.params.home ∧
      (demoQueueState (k + 1)).goal = Instances.liftPick ∧ (demoQueueState (k + 1)).start = 0 := by
  unfold demoQueueState
  simp only [Nat.add_one_ne_zero, ↓reduceIte]
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

/-- The program on the queue supervisor at a boundary with no request, from a busy state, sends
only the busy action and applies it with the queue supervisor's `step`. A design statement, not
from MLS. -/
theorem queue_boundary_busy {cfg : PolicyQueue.Config} {k : ℕ} {smp : Policy.Sample}
    {st : PolicyQueue.State} (h : st.sup.busy = true) :
    PolicyQueue.boundary cfg k [] smp st =
      (SupervisorQueue.step cfg.qsup st.sup (PolicyQueue.busyAction cfg k st smp)).map
        fun s' => ([PolicyQueue.busyAction cfg k st smp], { st with sup := s' }) := by
  unfold PolicyQueue.boundary
  simp only [PolicyQueue.requestActions, List.map_nil, SupervisorQueue.run, h, ↓reduceIte,
    List.nil_append]
  cases SupervisorQueue.step cfg.qsup st.sup (PolicyQueue.busyAction cfg k st smp) <;> rfl

/-- **The demonstration run is a run of the program on the queue supervisor.** On the requests
`demoQueueReqs` and the samples `demoSamples`, the program `PolicyQueue.boundary` at the
configuration `PolicyQueue.designNominalGain50` produces exactly the states `demoQueueState` and
the actions `demoQueueActs`: request and admission at boundary 0 (`k/10` s), ticks at 1 to 19, the
finish at 20 on the arrival test, nothing afterwards. A design statement, not from MLS. -/
theorem demoQueue_isProgramRun :
    PolicyQueue.IsProgramRun PolicyQueue.designNominalGain50 demoQueueReqs demoSamples
      demoQueueState demoQueueActs := by
  refine ⟨rfl, fun k => ?_⟩
  rcases Nat.lt_or_ge k 21 with hk | hk
  · rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rfl
    · have hr : demoQueueReqs k = [] := by simp [demoQueueReqs, hpos.ne']
      rw [hr]
      rcases Nat.lt_or_ge k 20 with hk20 | hk20
      · have hc : demoQueueState k =
            ⟨demoBusy (k - 1), Instances.params.home, Instances.liftPick, 0⟩ := by
          simp [demoQueueState, hpos.ne', show k ≤ 20 by omega]
        have hc' : demoQueueState (k + 1) =
            ⟨demoBusy k, Instances.params.home, Instances.liftPick, 0⟩ := by
          simp [demoQueueState, show k + 1 ≤ 20 by omega]
        have ha : demoQueueActs k = [.tick] := by simp [demoQueueActs, hpos.ne', hk20]
        rw [hc, hc', ha, queue_boundary_busy rfl]
        have hb : PolicyQueue.busyAction PolicyQueue.designNominalGain50 k
            ⟨demoBusy (k - 1), Instances.params.home, Instances.liftPick, 0⟩ (demoSamples k) =
              .tick := by
          have hdue : Policy.due PolicyQueue.designNominalGain50.toConfig
              (⟨demoBusy (k - 1), Instances.params.home, Instances.liftPick, 0⟩ :
                PolicyQueue.State).toPolicy k = false := by
            unfold Policy.due
            rw [decide_eq_false_iff_not]
            have : (k : ℚ) ≤ 19 := by exact_mod_cast (show k ≤ 19 by omega)
            show ¬ ((0 : ℕ) : ℚ) * (1 / 10) + 2 ≤ (k : ℚ) * (1 / 10)
            push_cast
            linarith
          unfold PolicyQueue.busyAction
          rw [hdue, Bool.false_and]
          simp only [Bool.false_eq_true, ↓reduceIte, demoBusy]
          have : k - 1 ≠ 25 := by omega
          simp [PolicyQueue.designNominalGain50, Policy.designNominalGain50, Instances.params, this]
        rw [hb]
        have hlt : k - 1 < 25 := by omega
        simp only [SupervisorQueue.step, SupervisorQueue.Action.blocker, demoBusy,
          PolicyQueue.Config.qsup, PolicyQueue.designNominalGain50, Policy.designNominalGain50,
          Instances.params, Bool.true_eq_false, ↓reduceIte, hlt, Option.map_some]
        simp [SupervisorQueue.effect, show k - 1 + 1 = k by omega]
      · have hk' : k = 20 := by omega
        subst hk'
        have hb : PolicyQueue.busyAction PolicyQueue.designNominalGain50 20
            ⟨demoBusy 19, Instances.params.home, Instances.liftPick, 0⟩ (demoSamples 20) =
              .finish := by
          unfold PolicyQueue.busyAction
          rw [show PolicyQueue.designNominalGain50.toConfig = Policy.designNominalGain50 from rfl]
          simp only
          rw [demoSamples_arrived]
          have hdue : Policy.due Policy.designNominalGain50
              (⟨demoBusy 19, Instances.params.home, Instances.liftPick, 0⟩ :
                PolicyQueue.State).toPolicy 20 = true := by decide +kernel
          rw [hdue]
          rfl
        show PolicyQueue.boundary PolicyQueue.designNominalGain50 20 [] (demoSamples 20)
          ⟨demoBusy 19, Instances.params.home, Instances.liftPick, 0⟩ =
            some ([.finish], ⟨demoDone, Instances.params.home, Instances.liftPick, 0⟩)
        rw [queue_boundary_busy rfl, hb]
        rfl
  · have hr : demoQueueReqs k = [] := by simp [demoQueueReqs, show k ≠ 0 by omega]
    have hc : demoQueueState k = ⟨demoDone, Instances.params.home, Instances.liftPick, 0⟩ := by
      simp [demoQueueState, show k ≠ 0 by omega, show ¬ k ≤ 20 by omega]
    have hc' : demoQueueState (k + 1) =
        ⟨demoDone, Instances.params.home, Instances.liftPick, 0⟩ := by
      simp [demoQueueState, show ¬ k + 1 ≤ 20 by omega]
    have ha : demoQueueActs k = [] := by
      simp [demoQueueActs, show k ≠ 0 by omega, show ¬ k < 20 by omega, show k ≠ 20 by omega]
    rw [hr, hc, hc', ha]
    rfl

/-- The demonstration run on the queue supervisor moves: the waypoint `(50, -35, 30)` (degrees) is
commanded after boundary 0 and reached after boundary 20, and the base yaw goes from `0` to `50°`
(radians, at `t = 0` and `t = 2` s). A design statement, not from MLS. -/
theorem demoQueue_moves :
    (demoQueueState 1).sup.commanded = [Instances.liftPick] ∧
      (demoQueueState 21).sup.current = Instances.liftPick ∧
      demoMotion 0 0 = 0 ∧ demoMotion 2 0 = 50 * Real.pi / 180 :=
  ⟨rfl, rfl, demoMotion_moves⟩

/-- The demonstration motion obeys the arm's equations of motion under computed torque at the gain
`50` rad/s tracking its own reference with zero disturbance, at every time `t` (s), within the
acceleration-level budget `50² · 3/100 = 75` rad/s². A design statement, not from MLS. -/
theorem demoMotion_follows_gain50 (t : ℝ) :
    CellArmFollowsAccelAt 50 2 (3 / 100) demoMotion demoVel demoAcc 0
      (DegPoint.toRad Instances.params.home) (DegPoint.toRad Instances.liftPick) 0 t := by
  refine ⟨hasDerivAt_moveRef _ _ _ _ t, hasDerivAt_moveRefDeriv _ _ _ _ t, fun i => ?_, ?_⟩
  · simp only [Matrix.mulVec_zero, Pi.zero_apply, abs_zero]
    positivity
  · simp [Control.RobotSystem.computedTorque, Control.computedTorqueAlong, demoMotion, demoVel,
      demoAcc]

/-- The demonstration motion starts in the tube of radius `3/100` rad around home at rest, at the
gain `50` rad/s. A design statement, not from MLS. -/
theorem demo_inTube_zero_gain50 :
    InTube (3 / 100) 50 (DegPoint.toRad Instances.params.home) 0 (demoMotion 0) (demoVel 0) := by
  intro i
  simp only [demoMotion, demoVel, moveRef_of_le (by norm_num : (0 : ℝ) < 2) le_rfl,
    moveRefDeriv_of_le (by norm_num : (0 : ℝ) < 2) le_rfl]
  simp only [sub_self, Pi.zero_apply, mul_zero, add_zero, abs_zero]
  exact ⟨by norm_num, by norm_num⟩

/-- **The hypotheses of the queue program-form theorem hold together on a moving run.** The
demonstration run meets the hypotheses `hprog`, `hsamp`, `htrack`, `hcont` and `h0` of
`cell_assured_program_measured_gain50_queue` (seconds, radians, radians per second; waypoints in
rational degrees). A design statement, not from MLS. -/
theorem cell_assured_program_measured_gain50_queue_hyps_demo :
    PolicyQueue.IsProgramRun PolicyQueue.designNominalGain50 demoQueueReqs demoSamples
      demoQueueState demoQueueActs ∧
    (∀ k : ℕ, ∀ i : Fin 3,
      |(demoSamples k).toRad PolicyQueue.designNominalGain50.toConfig i -
          demoMotion (k * (1 / 10)) i| ≤ 1 / 50 ∧
        |(demoSamples k).velRad i - demoVel (k * (1 / 10)) i| ≤ 3 / 10) ∧
    (∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelRightAt 50 2 (3 / 100) demoMotion demoVel demoAcc 0
        (DegPoint.toRad (demoQueueState (k + 1)).src) (DegPoint.toRad (demoQueueState (k + 1)).goal)
        ((demoQueueState (k + 1)).start * (1 / 10)) t) ∧
    ContinuousOn (fun s => (demoMotion s, demoVel s)) (Ici 0) ∧
    InTube (3 / 100) 50 (DegPoint.toRad Instances.params.home) 0 (demoMotion 0) (demoVel 0) := by
  refine ⟨demoQueue_isProgramRun, demoSamples_within, fun k t _ => ?_, demo_continuousOn,
    demo_inTube_zero_gain50⟩
  obtain ⟨h1, h2, h3⟩ := demoQueueState_succ_move k
  rw [h1, h2, h3]
  simpa using (demoMotion_follows_gain50 t).right

/-- **The queue program-form theorem for a moving run.** For the demonstration run on the queue
supervisor, the links keep `9/100` m from every obstacle at every `t ≥ 0` (s), the supervisor never
faults and its age stays below 25, the admitted move keeps the supervisor busy for 20 boundaries
and is finished with the arm at its goal, and at the finish the tool is within `219/5000` m of the
goal's tool position; the queue supervisor's contract is
`SupervisorQueue.contract_of_queue_invariant`. A design statement, not from MLS. -/
theorem program_queue_demo_gain50_assured :
    (∀ t, 0 ≤ t → sceneClear (demoMotion t)) ∧
    (∀ k, (demoQueueState k).sup.faulted = false ∧ (demoQueueState k).sup.age < 25) ∧
    (∀ k₀, (demoQueueState k₀).sup.busy = false → (demoQueueState (k₀ + 1)).sup.busy = true →
      (∀ j, j < 20 → (demoQueueState (k₀ + 1 + j)).sup.busy = true) ∧
      (demoQueueState (k₀ + 20 + 1)).sup.busy = false ∧
      (demoQueueState (k₀ + 20 + 1)).sup.current = (demoQueueState (k₀ + 1)).goal) ∧
    (∀ k, (demoQueueState k).sup.busy = true → (demoQueueState (k + 1)).sup.busy = false →
      dist (sceneTool (demoMotion (k * (1 / 10))))
        (sceneTool (DegPoint.toRad (demoQueueState k).goal)) ≤ 219 / 5000) := by
  obtain ⟨hprog, hsamp, htrack, hcont, h0⟩ := cell_assured_program_measured_gain50_queue_hyps_demo
  exact cell_assured_program_measured_gain50_queue
    (SupervisorQueue.contract_of_queue_invariant _) hprog hsamp htrack hcont h0

/-- The requests of the demonstration run on the request-set supervisor: the waypoint above the
pick slot `(50, -35, 30)` (degrees) at boundary 0, nothing afterwards. A design definition, not from
MLS. -/
def demoSetReqs (k : ℕ) : List Waypoint :=
  if k = 0 then [Instances.liftPick] else []

/-- The states of the program on the request-set supervisor in the demonstration run: the initial
state before boundary 0, busy with age `k - 1` on the move from home `(0, -40, 30)` to
`(50, -35, 30)` (degrees, admitted at boundary 0) before the boundaries `1, …, 20`, idle at the goal
from boundary 21 on, with no pending request. A design definition, not from MLS. -/
def demoSetState (k : ℕ) : Policy.State :=
  if k = 0 then Policy.State.init Policy.designNominalGain50
  else if k ≤ 20 then ⟨demoBusy (k - 1), Instances.params.home, Instances.liftPick, 0, []⟩
  else ⟨demoDone, Instances.params.home, Instances.liftPick, 0, []⟩

/-- The actions the program sends to the request-set supervisor in the demonstration run: request
and admission of `(50, -35, 30)` at boundary 0, `tick` at `1, …, 19`, `finish` at 20, nothing
afterwards. A design definition, not from MLS. -/
def demoSetActs (k : ℕ) : List Action :=
  if k = 0 then [.request Instances.liftPick, .admit Instances.liftPick]
  else if k < 20 then [.tick] else if k = 20 then [.finish] else []

/-- After every boundary the controller's record in the request-set run is the move from home to
the waypoint above the pick slot admitted at boundary 0. A design statement, not from MLS. -/
theorem demoSetState_succ_move (k : ℕ) :
    (demoSetState (k + 1)).src = Instances.params.home ∧
      (demoSetState (k + 1)).goal = Instances.liftPick ∧ (demoSetState (k + 1)).start = 0 := by
  unfold demoSetState
  simp only [Nat.add_one_ne_zero, ↓reduceIte]
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

/-- The program on the request-set supervisor at a boundary with no request, from a busy state,
sends only the busy action and applies it with the supervisor's `step`. A design statement, not
from MLS. -/
theorem set_boundary_busy {cfg : Policy.Config} {k : ℕ} {smp : Policy.Sample}
    {st : Policy.State} (h : st.sup.busy = true) :
    Policy.boundary cfg k [] smp st =
      (step cfg.sup st.sup (Policy.busyAction cfg k st smp)).map
        fun s' => ([Policy.busyAction cfg k st smp], { st with sup := s' }) := by
  unfold Policy.boundary
  simp only [h, ↓reduceIte, List.append_nil]
  cases step cfg.sup st.sup (Policy.busyAction cfg k st smp) <;> rfl

/-- **The demonstration run is a run of the program on the request-set supervisor.** On the
requests `demoSetReqs` and the samples `demoSamples`, the program `Policy.boundary` at the
configuration `Policy.designNominalGain50` produces exactly the states `demoSetState` and the
actions `demoSetActs`: request and admission at boundary 0 (`k/10` s), ticks at 1 to 19, the finish
at 20 on the arrival test, nothing afterwards. A design statement, not from MLS. -/
theorem demoSet_isProgramRun :
    Policy.IsProgramRun Policy.designNominalGain50 demoSetReqs demoSamples demoSetState
      demoSetActs := by
  refine ⟨rfl, fun k => ?_⟩
  rcases Nat.lt_or_ge k 21 with hk | hk
  · rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rfl
    · have hr : demoSetReqs k = [] := by simp [demoSetReqs, hpos.ne']
      rw [hr]
      rcases Nat.lt_or_ge k 20 with hk20 | hk20
      · have hc : demoSetState k =
            ⟨demoBusy (k - 1), Instances.params.home, Instances.liftPick, 0, []⟩ := by
          simp [demoSetState, hpos.ne', show k ≤ 20 by omega]
        have hc' : demoSetState (k + 1) =
            ⟨demoBusy k, Instances.params.home, Instances.liftPick, 0, []⟩ := by
          simp [demoSetState, show k + 1 ≤ 20 by omega]
        have ha : demoSetActs k = [.tick] := by simp [demoSetActs, hpos.ne', hk20]
        rw [hc, hc', ha, set_boundary_busy rfl]
        have hb : Policy.busyAction Policy.designNominalGain50 k
            ⟨demoBusy (k - 1), Instances.params.home, Instances.liftPick, 0, []⟩ (demoSamples k) =
              .tick := by
          have hdue : Policy.due Policy.designNominalGain50
              ⟨demoBusy (k - 1), Instances.params.home, Instances.liftPick, 0, []⟩ k = false := by
            unfold Policy.due
            rw [decide_eq_false_iff_not]
            have : (k : ℚ) ≤ 19 := by exact_mod_cast (show k ≤ 19 by omega)
            show ¬ ((0 : ℕ) : ℚ) * (1 / 10) + 2 ≤ (k : ℚ) * (1 / 10)
            push_cast
            linarith
          unfold Policy.busyAction
          rw [hdue, Bool.false_and]
          simp only [Bool.false_eq_true, ↓reduceIte, demoBusy]
          have : k - 1 ≠ 25 := by omega
          simp [Policy.designNominalGain50, Instances.params, this]
        rw [hb]
        have hlt : k - 1 < 25 := by omega
        simp only [step, Action.blocker, demoBusy, Policy.designNominalGain50, Instances.params,
          Bool.true_eq_false, ↓reduceIte, hlt, Option.map_some]
        simp [State.apply, show k - 1 + 1 = k by omega]
      · have hk' : k = 20 := by omega
        subst hk'
        have hb : Policy.busyAction Policy.designNominalGain50 20
            ⟨demoBusy 19, Instances.params.home, Instances.liftPick, 0, []⟩ (demoSamples 20) =
              .finish := by
          unfold Policy.busyAction
          simp only
          rw [demoSamples_arrived]
          have hdue : Policy.due Policy.designNominalGain50
              ⟨demoBusy 19, Instances.params.home, Instances.liftPick, 0, []⟩ 20 = true := by
            decide +kernel
          rw [hdue]
          rfl
        show Policy.boundary Policy.designNominalGain50 20 [] (demoSamples 20)
          ⟨demoBusy 19, Instances.params.home, Instances.liftPick, 0, []⟩ =
            some ([.finish], ⟨demoDone, Instances.params.home, Instances.liftPick, 0, []⟩)
        rw [set_boundary_busy rfl, hb]
        rfl
  · have hr : demoSetReqs k = [] := by simp [demoSetReqs, show k ≠ 0 by omega]
    have hc : demoSetState k = ⟨demoDone, Instances.params.home, Instances.liftPick, 0, []⟩ := by
      simp [demoSetState, show k ≠ 0 by omega, show ¬ k ≤ 20 by omega]
    have hc' : demoSetState (k + 1) =
        ⟨demoDone, Instances.params.home, Instances.liftPick, 0, []⟩ := by
      simp [demoSetState, show ¬ k + 1 ≤ 20 by omega]
    have ha : demoSetActs k = [] := by
      simp [demoSetActs, show k ≠ 0 by omega, show ¬ k < 20 by omega, show k ≠ 20 by omega]
    rw [hr, hc, hc', ha]
    rfl

/-- **The hypotheses of the request-set program-form theorem hold together on a moving run.** The
demonstration run meets the hypotheses `hprog`, `hsamp`, `htrack`, `hcont` and `h0` of
`cell_assured_program_measured_gain50` (seconds, radians, radians per second; waypoints in rational
degrees). A design statement, not from MLS. -/
theorem cell_assured_program_measured_gain50_hyps_demo :
    Policy.IsProgramRun Policy.designNominalGain50 demoSetReqs demoSamples demoSetState
      demoSetActs ∧
    (∀ k : ℕ, ∀ i : Fin 3,
      |(demoSamples k).toRad Policy.designNominalGain50 i - demoMotion (k * (1 / 10)) i| ≤ 1 / 50 ∧
        |(demoSamples k).velRad i - demoVel (k * (1 / 10)) i| ≤ 3 / 10) ∧
    (∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelRightAt 50 2 (3 / 100) demoMotion demoVel demoAcc 0
        (DegPoint.toRad (demoSetState (k + 1)).src) (DegPoint.toRad (demoSetState (k + 1)).goal)
        ((demoSetState (k + 1)).start * (1 / 10)) t) ∧
    ContinuousOn (fun s => (demoMotion s, demoVel s)) (Ici 0) ∧
    InTube (3 / 100) 50 (DegPoint.toRad Instances.params.home) 0 (demoMotion 0) (demoVel 0) := by
  refine ⟨demoSet_isProgramRun, demoSamples_within, fun k t _ => ?_, demo_continuousOn,
    demo_inTube_zero_gain50⟩
  obtain ⟨h1, h2, h3⟩ := demoSetState_succ_move k
  rw [h1, h2, h3]
  simpa using (demoMotion_follows_gain50 t).right

/-- **The request-set program-form theorem for a moving run.** For the demonstration run on the
request-set supervisor, the conclusions of `cell_assured_program_measured_gain50` hold: clearance of
`9/100` m at every `t ≥ 0` (s), no fault and age below 25, the admitted move busy for 20 boundaries
and finished with the arm at its goal, and the tool within `219/5000` m of the goal's tool position
at the finish; the supervisor's contract is `Supervisor.contract_of_design`. A design statement,
not from MLS. -/
theorem program_demo_gain50_assured :
    (∀ t, 0 ≤ t → sceneClear (demoMotion t)) ∧
    (∀ k, (demoSetState k).sup.faulted = false ∧ (demoSetState k).sup.age < 25) ∧
    (∀ k₀, (demoSetState k₀).sup.busy = false → (demoSetState (k₀ + 1)).sup.busy = true →
      (∀ j, j < 20 → (demoSetState (k₀ + 1 + j)).sup.busy = true) ∧
      (demoSetState (k₀ + 20 + 1)).sup.busy = false ∧
      (demoSetState (k₀ + 20 + 1)).sup.current = (demoSetState (k₀ + 1)).goal) ∧
    (∀ k, (demoSetState k).sup.busy = true → (demoSetState (k + 1)).sup.busy = false →
      dist (sceneTool (demoMotion (k * (1 / 10))))
        (sceneTool (DegPoint.toRad (demoSetState k).goal)) ≤ 219 / 5000) := by
  obtain ⟨hprog, hsamp, htrack, hcont, h0⟩ := cell_assured_program_measured_gain50_hyps_demo
  exact cell_assured_program_measured_gain50 (Supervisor.contract_of_design _) hprog hsamp htrack
    hcont h0

end RoboLean.Cell.Loop
