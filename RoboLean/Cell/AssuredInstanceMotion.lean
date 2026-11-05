import RoboLean.Cell.AssuredInstance

/-!
# A moving run of the assured cell

A satisfying instance of `cell_assured_accel_design` with a moving arm, to show that its
hypotheses hold together on concrete data. The planner requests the waypoint above the pick slot,
`(50°, −35°, 30°)`, which shares the crossing cell with home `(0°, −40°, 30°)`; the supervisor
admits it at boundary 0, ticks at the boundaries 1 to 19, finishes at boundary 20 and stays idle
afterwards. The arm follows the quintic reference of the move exactly, with zero disturbance:
`x = moveRef`, `v = moveRefDeriv`, `acc = moveRefDeriv2`, which satisfy the arm's equations of
motion under computed torque (`demoMotion_follows`). The theorem then gives, for this moving arm,
clearance from every obstacle at every instant and the tool within `73/1000` m of its goal at the
finish.

A design statement, not from MLS. The motion is the exact tracking of the reference, so it says
nothing about how large a disturbance a real arm meets; it only shows that the hypotheses are not
vacuous for a motion that moves between two waypoints.
-/

noncomputable section

namespace RoboLean.Cell.Loop

open Set Supervisor

/-- The joint positions of the demonstration motion: the quintic reference of the move from home
to the waypoint above the pick slot, started at time 0 with duration 2 s (radians). A design
definition, not from MLS. -/
def demoMotion (t : ℝ) : Fin 3 → ℝ :=
  moveRef (DegPoint.toRad Instances.params.home) (DegPoint.toRad Instances.liftPick) 0 2 t

/-- The joint velocities of the demonstration motion (radians per second). A design definition,
not from MLS. -/
def demoVel (t : ℝ) : Fin 3 → ℝ :=
  moveRefDeriv (DegPoint.toRad Instances.params.home) (DegPoint.toRad Instances.liftPick) 0 2 t

/-- The joint accelerations of the demonstration motion (radians per second squared). A design
definition, not from MLS. -/
def demoAcc (t : ℝ) : Fin 3 → ℝ :=
  moveRefDeriv2 (DegPoint.toRad Instances.params.home) (DegPoint.toRad Instances.liftPick) 0 2 t

/-- The supervisor's state during the move, with age `j`. A design definition, not from MLS. -/
def demoBusy (j : ℕ) : Supervisor.State :=
  ⟨[], [Instances.liftPick], [], [], true, false, j, Instances.params.home⟩

/-- The supervisor's state after the move. A design definition, not from MLS. -/
def demoDone : Supervisor.State :=
  ⟨[], [], [], [], false, false, 0, Instances.liftPick⟩

/-- The loop states of the demonstration run: initial before boundary 0, busy with age `k − 1`
before the boundaries `1, …, 20`, idle at the goal from boundary 21 on. A design definition, not
from MLS. -/
def demoState (k : ℕ) : CellState :=
  if k = 0 then CellState.init Instances.params.home
  else if k ≤ 20 then ⟨demoBusy (k - 1), Instances.params.home, Instances.liftPick, 0⟩
  else ⟨demoDone, Instances.params.home, Instances.liftPick, 0⟩

/-- The actions sent at the boundaries of the demonstration run: request and admit at 0, a tick
at `1, …, 19`, finish at 20, nothing afterwards. A design definition, not from MLS. -/
def demoActs (k : ℕ) : List Action :=
  if k = 0 then [.request Instances.liftPick, .admit Instances.liftPick]
  else if k < 20 then [.tick] else if k = 20 then [.finish] else []

/-- The move recorded after every boundary is the move from home to the waypoint above the pick
slot admitted at boundary 0. A design statement, not from MLS. -/
theorem demoState_succ_move (k : ℕ) :
    (demoState (k + 1)).src = Instances.params.home ∧
      (demoState (k + 1)).goal = Instances.liftPick ∧ (demoState (k + 1)).start = 0 := by
  unfold demoState
  simp only [Nat.add_one_ne_zero, ↓reduceIte]
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

/-- The demonstration motion obeys the arm's equations of motion under computed torque tracking
its own reference with zero disturbance, at every time. A design statement, not from MLS. -/
theorem demoMotion_follows (t : ℝ) :
    CellArmFollowsAccelAt 80 2 (1 / 20) demoMotion demoVel demoAcc 0
      (DegPoint.toRad Instances.params.home) (DegPoint.toRad Instances.liftPick) 0 t := by
  refine ⟨hasDerivAt_moveRef _ _ _ _ t, hasDerivAt_moveRefDeriv _ _ _ _ t, fun i => ?_, ?_⟩
  · simp
  · simp [Control.RobotSystem.computedTorque, Control.computedTorqueAlong, demoMotion, demoVel,
      demoAcc]

/-- The demonstration run is a timed run of the cell loop at the design values. A design
statement, not from MLS. -/
theorem demo_isCellRun :
    IsCellRun (cellParams (1 / 10) 2 (1 / 20) 8) Instances.params demoMotion demoVel demoState
      demoActs := by
  refine ⟨rfl, fun k => ?_⟩
  rcases Nat.lt_or_ge k 21 with hk | hk
  · rcases Nat.eq_zero_or_pos k with rfl | hpos
    · -- boundary 0: request, then admit
      refine ⟨[.request Instances.liftPick], [.admit Instances.liftPick],
        { Supervisor.State.init Instances.params.home with requested := [Instances.liftPick] },
        rfl, by simp [IsQueueAction], by decide +kernel, ?_⟩
      have : demoState (0 + 1) = ⟨demoBusy 0,
          ({ CellState.init Instances.params.home with
            sup := { Supervisor.State.init Instances.params.home with
              requested := [Instances.liftPick] } } : CellState).sup.current,
          Instances.liftPick, 0⟩ := rfl
      rw [this]
      exact PolicyStep.admit _ _ _ rfl (by decide +kernel)
    · rcases Nat.lt_or_ge k 20 with hk20 | hk20
      · -- boundaries 1 to 19: tick
        have hc : demoState k = ⟨demoBusy (k - 1), Instances.params.home, Instances.liftPick, 0⟩ := by
          simp [demoState, hpos.ne', show k ≤ 20 by omega]
        have hc' : demoState (k + 1) =
            ⟨demoBusy k, Instances.params.home, Instances.liftPick, 0⟩ := by
          simp [demoState, show k + 1 ≤ 20 by omega]
        have ha : demoActs k = [.tick] := by simp [demoActs, hpos.ne', hk20]
        rw [hc, hc', ha]
        refine ⟨[], [.tick], demoBusy (k - 1), rfl, by simp, rfl, ?_⟩
        have e : (⟨demoBusy k, Instances.params.home, Instances.liftPick, 0⟩ : CellState) =
            { (⟨demoBusy (k - 1), Instances.params.home, Instances.liftPick, 0⟩ : CellState) with
              sup := { demoBusy (k - 1) with age := k - 1 + 1 } } := by
          simp [demoBusy, show k - 1 + 1 = k by omega]
        simp only at e ⊢
        rw [e]
        refine PolicyStep.tick _ _ rfl ?_ ?_ ?_
        · rintro ⟨hdue, -⟩
          simp only [Due, CellState.toLoop, cellParams] at hdue
          have : (k : ℝ) ≤ 19 := by exact_mod_cast (show k ≤ 19 by omega)
          push_cast at hdue
          linarith
        · simp [demoBusy, Instances.params]; omega
        · have hlt : k - 1 < 25 := by omega
          simp only [step, Action.blocker, demoBusy, Instances.params, Bool.true_eq_false,
            ↓reduceIte, hlt]
          rfl
      · -- boundary 20: finish
        have hk' : k = 20 := by omega
        subst hk'
        have hc : demoState 20 = ⟨demoBusy 19, Instances.params.home, Instances.liftPick, 0⟩ := rfl
        rw [hc]
        refine ⟨[], [.finish], demoBusy 19, rfl, by simp, rfl, ?_⟩
        have e : demoState (20 + 1) =
            { (⟨demoBusy 19, Instances.params.home, Instances.liftPick, 0⟩ : CellState) with
              sup := demoDone } := rfl
        rw [e]
        refine PolicyStep.finish _ _ rfl ?_ ?_ (by decide +kernel)
        · simp only [Due, CellState.toLoop, cellParams]; norm_num
        · intro i
          have h2 : (0 : ℝ) + 2 ≤ ((20 : ℕ) : ℝ) * (1 / 10) := by norm_num
          simp only [cellParams, demoMotion, demoVel, moveRef_of_ge (by norm_num : (0 : ℝ) < 2) h2,
            moveRefDeriv_of_ge (by norm_num : (0 : ℝ) < 2) h2]
          norm_num
  · -- boundaries from 21 on: idle, nothing sent
    have hc : demoState k = ⟨demoDone, Instances.params.home, Instances.liftPick, 0⟩ := by
      simp [demoState, show k ≠ 0 by omega, show ¬ k ≤ 20 by omega]
    have hc' : demoState (k + 1) = ⟨demoDone, Instances.params.home, Instances.liftPick, 0⟩ := by
      simp [demoState, show ¬ k + 1 ≤ 20 by omega]
    have ha : demoActs k = [] := by
      simp [demoActs, show k ≠ 0 by omega, show ¬ k < 20 by omega, show k ≠ 20 by omega]
    rw [hc, hc', ha]
    exact ⟨[], [], demoDone, rfl, by simp, rfl, PolicyStep.wait _ rfl⟩

/-- **The assured cell for a moving arm.** For the demonstration run (the move from home to the
waypoint above the pick slot, admitted at boundary 0 and tracked exactly with zero disturbance),
every hypothesis of `cell_assured_accel_design` holds, so the links keep `9/100` m from every
obstacle at every `t ≥ 0`, the supervisor never faults, and at the finish the tool is within
`73/1000` m of the goal's tool position. A design statement, not from MLS. -/
theorem demo_assured :
    (∀ t, 0 ≤ t → sceneClear (demoMotion t)) ∧
    (∀ k, (demoState k).sup.faulted = false ∧ (demoState k).sup.age < 25) ∧
    (∀ k, (demoState k).sup.busy = true → (demoState (k + 1)).sup.busy = false →
      dist (sceneTool (demoMotion (k * (1 / 10))))
        (sceneTool (DegPoint.toRad (demoState k).goal)) ≤ 73 / 1000) := by
  have hcont : ContinuousOn (fun s => (demoMotion s, demoVel s)) (Ici 0) :=
    (continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_moveRef _ _ _ _ t).continuousAt.prodMk
        (hasDerivAt_moveRefDeriv _ _ _ _ t).continuousAt).continuousOn
  have htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelAt 80 2 (1 / 20) demoMotion demoVel demoAcc 0
        (DegPoint.toRad (demoState (k + 1)).src) (DegPoint.toRad (demoState (k + 1)).goal)
        ((demoState (k + 1)).start * (1 / 10)) t := by
    intro k t _
    obtain ⟨h1, h2, h3⟩ := demoState_succ_move k
    rw [h1, h2, h3]
    simpa using demoMotion_follows t
  have h0 : InTube (1 / 20) 80 (DegPoint.toRad Instances.params.home) 0 (demoMotion 0)
      (demoVel 0) := by
    intro i
    simp only [demoMotion, demoVel, moveRef_of_le (by norm_num : (0 : ℝ) < 2) le_rfl,
      moveRefDeriv_of_le (by norm_num : (0 : ℝ) < 2) le_rfl]
    norm_num
  obtain ⟨hclear, hfault, -, htool⟩ :=
    cell_assured_accel_design demo_isCellRun htrack hcont h0
  exact ⟨hclear, hfault, htool⟩

/-- The demonstration motion obeys the arm's equations of motion under computed torque tracking
its own reference with zero disturbance, in the torque-norm form with `d̄ = 0`. A design
statement, not from MLS. -/
theorem demoMotion_follows_torque (t : ℝ) :
    CellArmFollowsAt 80 2 0 demoMotion demoVel demoAcc 0
      (DegPoint.toRad Instances.params.home) (DegPoint.toRad Instances.liftPick) 0 t := by
  refine ⟨hasDerivAt_moveRef _ _ _ _ t, hasDerivAt_moveRefDeriv _ _ _ _ t, by simp, ?_⟩
  simp [Control.RobotSystem.computedTorque, Control.computedTorqueAlong, demoMotion, demoVel,
    demoAcc]

/-- **The assured cell for a moving arm, torque-norm form.** The demonstration run meets every
hypothesis of `cell_assured_torque_design` with `d̄ = 0`, so its conclusions hold for it. A
design statement, not from MLS. -/
theorem demo_assured_torque :
    (∀ t, 0 ≤ t → sceneClear (demoMotion t)) ∧
    (∀ k, (demoState k).sup.faulted = false ∧ (demoState k).sup.age < 25) := by
  have hcont : ContinuousOn (fun s => (demoMotion s, demoVel s)) (Ici 0) :=
    (continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_moveRef _ _ _ _ t).continuousAt.prodMk
        (hasDerivAt_moveRefDeriv _ _ _ _ t).continuousAt).continuousOn
  have htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAt 80 2 0 demoMotion demoVel demoAcc 0
        (DegPoint.toRad (demoState (k + 1)).src) (DegPoint.toRad (demoState (k + 1)).goal)
        ((demoState (k + 1)).start * (1 / 10)) t := by
    intro k t _
    obtain ⟨h1, h2, h3⟩ := demoState_succ_move k
    rw [h1, h2, h3]
    simpa using demoMotion_follows_torque t
  have h0 : InTube (1 / 20) 80 (DegPoint.toRad Instances.params.home) 0 (demoMotion 0)
      (demoVel 0) := by
    intro i
    simp only [demoMotion, demoVel, moveRef_of_le (by norm_num : (0 : ℝ) < 2) le_rfl,
      moveRefDeriv_of_le (by norm_num : (0 : ℝ) < 2) le_rfl]
    norm_num
  obtain ⟨hclear, hfault, -, -⟩ :=
    cell_assured_torque_design le_rfl (by norm_num) demo_isCellRun htrack hcont h0
  exact ⟨hclear, hfault⟩

/-- The demonstration motion moves: its base yaw goes from `0` to `50°`. A design statement, not
from MLS. -/
theorem demoMotion_moves : demoMotion 0 0 = 0 ∧ demoMotion 2 0 = 50 * Real.pi / 180 := by
  constructor
  · simp [demoMotion, moveRef_of_le (by norm_num : (0 : ℝ) < 2) le_rfl, DegPoint.toRad, degToRad,
      Instances.params]
  · simp [demoMotion, moveRef_of_ge (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) + 2 ≤ 2),
      DegPoint.toRad, degToRad, Instances.liftPick]

end RoboLean.Cell.Loop
