import RoboLean.Cell.AssuredContract

/-!
# The loop-level contract cannot be dropped

`OpenHyps.assured` (in `RoboLean.Cell.LoopOpen`) concludes clearance at every instant for an open
run of the sampled loop under `OpenHyps`, given the loop-level contract `LoopContract` (a busy
loop's move is linked; a faulted supervisor is idle) and certified cells. This file shows that the
contract is not implied by the other hypotheses: it constructs one open run, on the cell's data,
that meets every field of `OpenHyps` and whose loop data are certified by the scene's cells
(`openCellParams_certify`), in which a move that is not linked is admitted, and along which the
clearance conclusion fails.

The run, at the period `1/10` s, the move duration `2` s, the tube radius and arrival position
tolerance `3/100` rad, the arrival speed tolerance `24/5` rad/s and the gain `80` rad/s: the arm
starts at rest at the pick slot `(60°, 0°, 30°)`, which lies in the pick cell and so is linked to
itself; at boundary 0 the open loop admits the place slot `(-60°, 0°, 15°)`, which lies in the
place cell only, so the program's link test on the two is `false` (`unlinked_not_linked`); it
ticks at the boundaries 1 to 19, finishes at boundary 20 with the arm exactly at the goal at rest,
and waits from then on. The arm follows the quintic reference of the move exactly, with zero
disturbance (`unlinkedMotion`, `unlinkedVel`, `unlinkedAcc`), which satisfies the arm's equations
of motion under computed torque with the acceleration from the right. At `t = 1` s the reference
is halfway along the straight joint-space segment from the pick slot to the place slot, where the
tool point lies in the divider (`straight_pick_place_hits_divider`), so the links keep no
clearance there (`unlinked_not_clear`).

* `unlinked_openHyps`: every hypothesis of `OpenHyps` holds for the run.
* `unlinked_not_linked`, `unlinked_not_loopContract`: the admitted move is not linked, so the run
  does not meet `LoopContract`.
* `unlinked_not_clear`: the clearance conclusion of `OpenHyps.assured` fails.
* `loopContract_necessary`: the summary.

What this shows: without the linkage that the loop-level contract supplies, the clearance
conclusion of the abstract theorem can fail although every other hypothesis holds, including the
cell certificate. What it does not show: it is one constructed run of the open loop, not a run of
the executable supervisor, which never admits this move (its link test rejects it); and like the
theorems it accompanies it concerns the ideal sampled loop and the ideal rigid-body model, not a
physical arm.

A design statement, not from MLS. Units: seconds, radians, radians per second; waypoints in
rational degrees, mapped to radians by `DegPoint.toRad`. The arm is `cellArm` (MLS Example 4.3,
printed p. 172, with the cell's parameters) under computed torque (MLS eq. (4.49), p. 191).
-/

noncomputable section

namespace RoboLean.Cell.Loop

open Set Supervisor

/-- The home waypoint of the run: the pick slot `(60°, 0°, 30°)`, in the pick cell only. A design
definition, not from MLS; degrees. -/
def unlinkedHome : Waypoint := (60, 0, 30)

/-- The goal admitted at boundary 0: the place slot `(-60°, 0°, 15°)`, in the place cell only. A
design definition, not from MLS; degrees. -/
def unlinkedGoal : Waypoint := (-60, 0, 15)

/-- The joint positions of the run: the quintic reference of the move from the pick slot to the
place slot, started at time 0 with duration 2 s (radians). A design definition, not from MLS. -/
def unlinkedMotion (t : ℝ) : Fin 3 → ℝ :=
  moveRef (DegPoint.toRad unlinkedHome) (DegPoint.toRad unlinkedGoal) 0 2 t

/-- The joint velocities of the run, the derivative of the reference (radians per second). A design
definition, not from MLS. -/
def unlinkedVel (t : ℝ) : Fin 3 → ℝ :=
  moveRefDeriv (DegPoint.toRad unlinkedHome) (DegPoint.toRad unlinkedGoal) 0 2 t

/-- The joint accelerations of the run, the second derivative of the reference (radians per second
squared). A design definition, not from MLS. -/
def unlinkedAcc (t : ℝ) : Fin 3 → ℝ :=
  moveRefDeriv2 (DegPoint.toRad unlinkedHome) (DegPoint.toRad unlinkedGoal) 0 2 t

/-- The tracking predicate of the run: the cell arm follows the quintic reference of the move from
`a` to `b` (waypoints in degrees, mapped to radians) admitted at `t₀`, with duration 2 s, gain
80 rad/s, tube radius `3/100` rad and zero disturbance, with the position and velocity of the run
having right derivatives (`CellArmFollowsAccelRightAt`; computed torque of MLS eq. (4.49),
p. 191). A design definition, not from MLS. -/
def unlinkedFollows (a b : Waypoint) (t₀ t : ℝ) : Prop :=
  CellArmFollowsAccelRightAt 80 2 (3 / 100) unlinkedMotion unlinkedVel unlinkedAcc 0
    (DegPoint.toRad a) (DegPoint.toRad b) t₀ t

/-- The loop states of the run: initial at the pick slot before boundary 0; busy with the move from
the pick slot to the place slot admitted at boundary 0, with age `k − 1`, before the boundaries
`1, …, 20`; idle at the place slot from boundary 21 on. A design definition, not from MLS. -/
def unlinkedState (k : ℕ) : Loop.State Waypoint :=
  if k = 0 then Loop.init unlinkedHome
  else if k ≤ 20 then ⟨unlinkedHome, true, false, k - 1, unlinkedHome, unlinkedGoal, 0⟩
  else ⟨unlinkedGoal, false, false, 0, unlinkedHome, unlinkedGoal, 0⟩

/-- The loop states of the run while busy, before the boundaries `1, …, 20`. A design statement,
not from MLS. -/
theorem unlinkedState_of_le {k : ℕ} (h0 : k ≠ 0) (h20 : k ≤ 20) :
    unlinkedState k = ⟨unlinkedHome, true, false, k - 1, unlinkedHome, unlinkedGoal, 0⟩ := by
  simp [unlinkedState, h0, h20]

/-- The loop states of the run after the finish, from boundary 21 on. A design statement, not from
MLS. -/
theorem unlinkedState_of_gt {k : ℕ} (h : 20 < k) :
    unlinkedState k = ⟨unlinkedGoal, false, false, 0, unlinkedHome, unlinkedGoal, 0⟩ := by
  simp [unlinkedState, show k ≠ 0 by omega, show ¬ k ≤ 20 by omega]

/-- After every boundary the recorded move is the one from the pick slot to the place slot
admitted at boundary 0. A design statement, not from MLS. -/
theorem unlinkedState_succ_move (k : ℕ) :
    (unlinkedState (k + 1)).src = unlinkedHome ∧ (unlinkedState (k + 1)).goal = unlinkedGoal ∧
      (unlinkedState (k + 1)).start = 0 := by
  unfold unlinkedState
  simp only [Nat.add_one_ne_zero, ↓reduceIte]
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

/-- **The program's link test rejects the move.** No cell of the instance contains both the pick
slot `(60°, 0°, 30°)` and the place slot `(-60°, 0°, 15°)`; checked by evaluation. A design
statement, not from MLS. -/
theorem unlinked_not_linked :
    Supervisor.linked Instances.params.cells unlinkedHome unlinkedGoal = false := by
  decide +kernel

/-- The pick slot is linked to itself by the program's link test (the pick cell contains it);
checked by evaluation. A design statement, not from MLS. -/
theorem unlinkedHome_linked :
    Supervisor.linked Instances.params.cells unlinkedHome unlinkedHome = true := by
  decide +kernel

/-- The quintic step is `1/2` at the normalized time `1/2`. A design statement, not from MLS. -/
theorem unlinked_quinticStep_half : quinticStep (1 / 2) = 1 / 2 := by
  have h : max (0 : ℝ) (min (1 / 2) 1) = 1 / 2 := by norm_num
  rw [quinticStep, h]
  norm_num

/-- The run follows its own reference exactly with zero disturbance at every time, with two-sided
derivatives. A design statement, not from MLS. -/
theorem unlinkedMotion_follows (t : ℝ) :
    CellArmFollowsAccelAt 80 2 (3 / 100) unlinkedMotion unlinkedVel unlinkedAcc 0
      (DegPoint.toRad unlinkedHome) (DegPoint.toRad unlinkedGoal) 0 t := by
  refine ⟨hasDerivAt_moveRef _ _ _ _ t, hasDerivAt_moveRefDeriv _ _ _ _ t, fun i => ?_, ?_⟩
  · simp only [Matrix.mulVec_zero, Pi.zero_apply, abs_zero]
    positivity
  · simp [Control.RobotSystem.computedTorque, Control.computedTorqueAlong, unlinkedMotion,
      unlinkedVel, unlinkedAcc]

/-- The position and velocity of the run are continuous on `[0, ∞)`. A design statement, not from
MLS. -/
theorem unlinked_continuousOn :
    ContinuousOn (fun s => (unlinkedMotion s, unlinkedVel s)) (Ici 0) :=
  (continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_moveRef _ _ _ _ t).continuousAt.prodMk
      (hasDerivAt_moveRefDeriv _ _ _ _ t).continuousAt).continuousOn

/-- **The run is a timed run of the open loop.** At boundary 0 the open loop admits the place slot
from the pick slot, ticks at the boundaries 1 to 19, finishes at boundary 20 (the move is due and
the arm is exactly at the goal at rest), and waits from then on. A design statement, not from
MLS. -/
theorem unlinked_isOpenRun :
    IsOpenRun (openCellParams (1 / 10) 2 (3 / 100) (24 / 5)) unlinkedHome unlinkedMotion
      unlinkedVel unlinkedState := by
  refine ⟨rfl, fun k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · -- boundary 0: admit the place slot
    exact OpenStep.admit (Loop.init unlinkedHome) unlinkedGoal rfl
  rcases Nat.lt_or_ge k 20 with hk20 | hk20
  · -- boundaries 1 to 19: tick
    rw [unlinkedState_of_le hpos.ne' (by omega), unlinkedState_of_le (by omega) (by omega)]
    have e : (⟨unlinkedHome, true, false, k + 1 - 1, unlinkedHome, unlinkedGoal, 0⟩ :
        Loop.State Waypoint) =
        { (⟨unlinkedHome, true, false, k - 1, unlinkedHome, unlinkedGoal, 0⟩ :
            Loop.State Waypoint) with age := k - 1 + 1 } := by
      rw [show k + 1 - 1 = k - 1 + 1 by omega]
    rw [e]
    refine OpenStep.tick _ rfl ?_ ?_
    · rintro ⟨hdue, -⟩
      simp only [Due, openCellParams] at hdue
      have : (k : ℝ) ≤ 19 := by exact_mod_cast (show k ≤ 19 by omega)
      push_cast at hdue
      linarith
    · simp only [openCellParams, Instances.params]
      omega
  rcases Nat.eq_or_lt_of_le hk20 with rfl | hk21
  · -- boundary 20: finish
    rw [unlinkedState_of_le (by omega) le_rfl, unlinkedState_of_gt (by omega)]
    refine OpenStep.finish _ rfl ?_ ?_
    · simp only [Due, openCellParams]
      norm_num
    · intro i
      have h2 : (0 : ℝ) + 2 ≤ ((20 : ℕ) : ℝ) * (1 / 10) := by norm_num
      simp only [openCellParams, unlinkedMotion, unlinkedVel,
        moveRef_of_ge (by norm_num : (0 : ℝ) < 2) h2,
        moveRefDeriv_of_ge (by norm_num : (0 : ℝ) < 2) h2]
      norm_num
  · -- boundaries from 21 on: wait
    rw [unlinkedState_of_gt hk21, unlinkedState_of_gt (by omega)]
    exact OpenStep.wait _ rfl

/-- **Every hypothesis of the open loop's theorem holds for the run.** For the cell's loop data at
the period `1/10` s, the move duration `2` s and the arrival tolerances `3/100` rad and `24/5`
rad/s, the quintic reference, the tube radius `3/100` rad and the gain `80` rad/s, the home
waypoint the pick slot, the arm's own tracking predicate `unlinkedFollows` and the run above:
the fields of `OpenHyps` hold, among them the move corollary for every linked move
(`cellArm_moveCorollary_accel_right`). A design statement, not from MLS. -/
theorem unlinked_openHyps :
    OpenHyps (openCellParams (1 / 10) 2 (3 / 100) (24 / 5))
      (quinticMoveRef (n := 3) (by norm_num : (0 : ℝ) < 2)) (3 / 100) 80 unlinkedHome
      unlinkedFollows unlinkedMotion unlinkedVel unlinkedState where
  period_pos := by show (0 : ℝ) < 1 / 10; norm_num
  duration_pos := by show (0 : ℝ) < 2; norm_num
  ceil_le_bound := by
    show ⌈(2 : ℝ) / (1 / 10)⌉₊ ≤ Instances.params.bound
    rw [design_steps]
    decide
  rate_nonneg := by norm_num
  radius_le_posTol := le_rfl
  speed_le_velTol := by show 2 * (80 : ℝ) * (3 / 100) ≤ 24 / 5; norm_num
  home_linked := unlinkedHome_linked
  run := unlinked_isOpenRun
  tracks := by
    intro k t _
    obtain ⟨h1, h2, h3⟩ := unlinkedState_succ_move k
    rw [h1, h2, h3]
    simpa [unlinkedFollows] using (unlinkedMotion_follows t).right
  move := cellArm_moveCorollary_accel_right (openCellParams (1 / 10) 2 (3 / 100) (24 / 5))
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 80) unlinked_continuousOn
  init_tube := by
    intro i
    simp only [openCellParams, unlinkedMotion, unlinkedVel,
      moveRef_of_le (by norm_num : (0 : ℝ) < 2) le_rfl,
      moveRefDeriv_of_le (by norm_num : (0 : ℝ) < 2) le_rfl]
    simp only [sub_self, Pi.zero_apply, mul_zero, add_zero, abs_zero]
    norm_num

/-- **The run does not meet the loop-level contract.** Before boundary 1 the loop is busy with the
move from the pick slot to the place slot, which the program's link test rejects. A design
statement, not from MLS. -/
theorem unlinked_not_loopContract :
    ¬ LoopContract (openCellParams (1 / 10) 2 (3 / 100) (24 / 5)) unlinkedState := by
  intro hc
  have h : Supervisor.linked Instances.params.cells unlinkedHome unlinkedGoal = true :=
    (hc 1).1 rfl
  rw [unlinked_not_linked] at h
  exact Bool.false_ne_true h

/-- At `t = 1` s the run is halfway along the straight joint-space segment from the pick slot to
the place slot. A design statement, not from MLS; radians. -/
theorem unlinkedMotion_one :
    unlinkedMotion 1 = fun i => DegPoint.toRad (60, 0, 30) i +
      (1 / 2 : ℝ) * (DegPoint.toRad (-60, 0, 15) i - DegPoint.toRad (60, 0, 30) i) := by
  have hq : quinticStep ((1 - 0) / 2) = 1 / 2 := by
    rw [show ((1 : ℝ) - 0) / 2 = 1 / 2 by norm_num, unlinked_quinticStep_half]
  funext i
  simp only [unlinkedMotion, moveRef, hq, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rfl

/-- **The clearance conclusion fails along the run.** At `t = 1` s the tool point lies in the
divider, so the links do not keep `9/100` m from every obstacle. A design statement, not from MLS;
seconds, metres. -/
theorem unlinked_not_clear : ¬ ∀ t, 0 ≤ t → sceneClear (unlinkedMotion t) := by
  intro h
  have h1 := h 1 zero_le_one divider (by simp [sceneObstacles])
  rw [unlinkedMotion_one] at h1
  exact straight_pick_place_not_clear (by rw [linkRadius_add_clearance]; norm_num) h1

/-- **The loop-level contract is necessary for the open loop's theorem.** There are a home
waypoint, a tracking predicate, a motion and a run of the open loop on the cell's data at the
period `1/10` s, the move duration `2` s, the tube radius `3/100` rad and the gain `80` rad/s
such that every hypothesis of `OpenHyps` holds and the scene's cells certify the loop data at the
inflation `1/20` rad, yet the run does not meet `LoopContract` and the clearance conclusion of
`OpenHyps.assured` fails. A design statement, not from MLS. -/
theorem loopContract_necessary :
    ∃ (home : Waypoint) (follows : Waypoint → Waypoint → ℝ → ℝ → Prop)
      (x v : ℝ → Fin 3 → ℝ) (s : ℕ → Loop.State Waypoint),
      OpenHyps (openCellParams (1 / 10) 2 (3 / 100) (24 / 5))
        (quinticMoveRef (n := 3) (by norm_num : (0 : ℝ) < 2)) (3 / 100) 80 home follows x v s ∧
      CellsCertify (openCellParams (1 / 10) 2 (3 / 100) (24 / 5)) cellInflation sceneClear ∧
      ¬ LoopContract (openCellParams (1 / 10) 2 (3 / 100) (24 / 5)) s ∧
      ¬ ∀ t, 0 ≤ t → sceneClear (x t) :=
  ⟨unlinkedHome, unlinkedFollows, unlinkedMotion, unlinkedVel, unlinkedState, unlinked_openHyps,
    openCellParams_certify _ _ _ _, unlinked_not_loopContract, unlinked_not_clear⟩

end RoboLean.Cell.Loop
