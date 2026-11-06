import RoboLean.Cell.AssuredContractInstance
import RoboLean.Cell.AssuredInstanceRightStep

/-!
# The hypotheses of the assured cell theorem hold together

The theorem `cell_assured_contract_design_tight_right` (gain `ω = 80` rad/s, tube radius
`δ = δ_a = 3/100` rad, period `h = 1/10` s, move duration `T = 2` s, `v_a = 24/5` rad/s) has, besides
the supervisor's contract, four hypotheses on a run: the timed run of the cell loop (`hrun`), the
per-period tracking with the acceleration from the right (`htrack`), the continuity of the
position and the velocity on `[0, ∞)` (`hcont`) and the start in the tube around home (`h0`). Each
lemma here states, in the theorem's own terms, that some run meets all four at once.

* `cell_assured_contract_hyps_demo`: the moving run from home to the waypoint above the pick slot,
  tracked exactly with zero disturbance.
* `cell_assured_contract_hyps_step`: the run at rest at home under a disturbance that switches on
  at `t = 1` s and produces the acceleration `192` rad/s² on the base joint, so that the
  acceleration jumps.

The supervisor's contract itself is proved by `Supervisor.contract_of_design`. These are design
statements, not from MLS (the arm is `cellArm`, MLS Example 4.3, printed p. 172, under computed
torque, MLS eq. (4.49), p. 191). They show that the hypotheses are not contradictory; they say
nothing about the disturbances a real arm meets.
-/

set_option autoImplicit false

noncomputable section

namespace RoboLean.Cell.Loop

open Set Supervisor

/-- **The hypotheses hold together on a moving run.** The demonstration run (the move from home to
the waypoint above the pick slot, tracked exactly with zero disturbance) meets the hypotheses
`hrun`, `htrack`, `hcont` and `h0` of `cell_assured_contract_design_tight_right` together (seconds,
radians, radians per second). A design statement, not from MLS. -/
theorem cell_assured_contract_hyps_demo :
    ∃ (x v acc d : ℝ → Fin 3 → ℝ) (c : ℕ → CellState) (acts : ℕ → List Action),
      IsCellRun (openCellParams (1 / 10) 2 (3 / 100) (24 / 5)) Instances.params x v c acts ∧
      (∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
        CellArmFollowsAccelRightAt 80 2 (3 / 100) x v acc d (DegPoint.toRad (c (k + 1)).src)
          (DegPoint.toRad (c (k + 1)).goal) ((c (k + 1)).start * (1 / 10)) t) ∧
      ContinuousOn (fun s => (x s, v s)) (Ici 0) ∧
      InTube (3 / 100) 80 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0) := by
  refine ⟨demoMotion, demoVel, demoAcc, 0, demoState, demoActs,
    (demo_isCellRun_of (by norm_num) (by norm_num)).openCellParams_of_cellParams, ?_,
    demo_continuousOn, demo_inTube_zero (by norm_num)⟩
  intro k t _
  obtain ⟨h1, h2, h3⟩ := demoState_succ_move k
  rw [h1, h2, h3]
  simpa using (demoMotion_follows_of (by norm_num) t).right

/-- **The hypotheses hold together on a run whose acceleration jumps.** The run at rest at home
with the supervisor idle, under a disturbance torque that switches on at `t = 1` s and produces
the acceleration `192` rad/s² on the base joint, meets the hypotheses `hrun`, `htrack`, `hcont`
and `h0` of `cell_assured_contract_design_tight_right` together (seconds, radians, radians per
second). A design statement, not from MLS. -/
theorem cell_assured_contract_hyps_step :
    ∃ (x v acc d : ℝ → Fin 3 → ℝ) (c : ℕ → CellState) (acts : ℕ → List Action),
      IsCellRun (openCellParams (1 / 10) 2 (3 / 100) (24 / 5)) Instances.params x v c acts ∧
      (∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
        CellArmFollowsAccelRightAt 80 2 (3 / 100) x v acc d (DegPoint.toRad (c (k + 1)).src)
          (DegPoint.toRad (c (k + 1)).goal) ((c (k + 1)).start * (1 / 10)) t) ∧
      ContinuousOn (fun s => (x s, v s)) (Ici 0) ∧
      InTube (3 / 100) 80 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0) := by
  refine ⟨stepMotion 192, stepVel 192, stepAcc 192, stepDist 192, idleState, idleActs,
    idle_isCellRun _ _ _, ?_, step_continuousOn 192, step_inTube_zero 192⟩
  intro k t _
  simpa [idleState, CellState.init] using
    stepMotion_follows_right (by norm_num : (0 : ℝ) ≤ 192) le_rfl t

end RoboLean.Cell.Loop
