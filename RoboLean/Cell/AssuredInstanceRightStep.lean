import RoboLean.Cell.AssuredInstanceRight

/-!
# A run of the assured cell whose acceleration jumps

A satisfying instance of `cell_assured_accel_design_tight_right` (gain `ω = 80` rad/s, tube
radius `δ = 3/100` rad) in which the disturbance is a step, so that the acceleration jumps: the
supervisor stays idle at home and the controller holds home, and at `t = 1` s (a sample
boundary) a disturbance torque switches on that produces the acceleration `c` rad/s² on the base
joint, `0 < c ≤ 192 = 80² · 3/100`. The error of the base joint, `s = t − 1` seconds after the
step, is the step response of `ë + 2ω ė + ω² e = c`,
`e(s) = (c/ω²)(1 − (1 + ω s) e^{−ω s})`, with `ė(s) = c s e^{−ω s}` and
`ë(s) = c (1 − ω s) e^{−ω s}` for `s ≥ 0`, all zero before the step; the velocity is continuous
and has a right derivative at every instant, but at `t = 1` its left derivative is `0` and its
right derivative is `c`.

* `stepMotion`, `stepVel`, `stepAcc`, `stepDist`, `idleState`, `idleActs`: the run.
* `idle_isCellRun`: the idle run is a timed run of the cell loop for every motion.
* `stepMotion_follows_right`: the motion meets `CellArmFollowsAccelRightAt` at every instant.
* `step_assured_tight_right`: hence the conclusions of `cell_assured_accel_design_tight_right`
  hold for it: both links keep `9/100` m from every obstacle at every `t ≥ 0`, and the supervisor
  never faults.
* `stepVel_not_differentiableAt`, `step_not_followsAccelAt`: the velocity has no two-sided
  derivative at `t = 1`, so no acceleration curve and no disturbance make the two-sided
  per-period hypothesis of `cell_assured_accel_design_tight` hold for this motion.

A design statement, not from MLS (the arm is `cellArm`, MLS Example 4.3, printed p. 172, under
computed torque, MLS eq. (4.49), p. 191). Radians, seconds, radians per second squared. The run
says nothing about the size of disturbances a real arm meets.
-/

noncomputable section

namespace RoboLean.Cell.Loop

open Matrix Set Supervisor

/-- The base joint's error `s` seconds after a step of `c` rad/s² in the acceleration the
disturbance produces, at the gain `80` rad/s: `(c/80²)(1 − (1 + 80 s) e^{−80 s})` for `s ≥ 0`,
zero for `s ≤ 0` (radians). A design definition, not from MLS. -/
def stepErr (c s : ℝ) : ℝ :=
  c / 80 ^ 2 * (1 - (1 + 80 * max s 0) * Real.exp (-(80 * max s 0)))

/-- The velocity of `stepErr`: `c s e^{−80 s}` for `s ≥ 0`, zero for `s ≤ 0` (radians per
second). A design definition, not from MLS. -/
def stepErrVel (c s : ℝ) : ℝ :=
  c * max s 0 * Real.exp (-(80 * max s 0))

/-- The acceleration of `stepErr` from the right: `c (1 − 80 s) e^{−80 s}` for `s ≥ 0`, zero for
`s < 0` (radians per second squared; it jumps from `0` to `c` at `s = 0`). A design definition,
not from MLS. -/
def stepErrAcc (c s : ℝ) : ℝ :=
  if 0 ≤ s then c * (1 - 80 * s) * Real.exp (-(80 * s)) else 0

/-- The joint positions of the step run: home, with the base joint displaced by `stepErr` of a
step at `t = 1` s (radians). A design definition, not from MLS. -/
def stepMotion (c t : ℝ) : Fin 3 → ℝ :=
  DegPoint.toRad Instances.params.home + Pi.single 0 (stepErr c (t - 1))

/-- The joint velocities of the step run (radians per second). A design definition, not from
MLS. -/
def stepVel (c t : ℝ) : Fin 3 → ℝ :=
  Pi.single 0 (stepErrVel c (t - 1))

/-- The joint accelerations of the step run, from the right (radians per second squared). A
design definition, not from MLS. -/
def stepAcc (c t : ℝ) : Fin 3 → ℝ :=
  Pi.single 0 (stepErrAcc c (t - 1))

/-- The disturbance torque of the step run: zero before `t = 1` s, and from `t = 1` s on the
torque `M(x(t)) (c, 0, 0)` that produces the acceleration `c` on the base joint (newton metres).
A design definition, not from MLS. -/
def stepDist (c t : ℝ) : Fin 3 → ℝ :=
  cellRobot.M (stepMotion c t) *ᵥ Pi.single 0 (if 1 ≤ t then c else 0)

/-- The loop states of the idle run: the initial state at home at every boundary. A design
definition, not from MLS. -/
def idleState : ℕ → CellState := fun _ => CellState.init Instances.params.home

/-- The actions of the idle run: nothing is sent at any boundary. A design definition, not from
MLS. -/
def idleActs : ℕ → List Action := fun _ => []

/-- A function equal to `g` on `[1, ∞)` and to zero on `(-∞, 1)` has, at every `t`, the right
derivative `g' t` for `t ≥ 1` and zero for `t < 1`. -/
private lemma hasDerivWithinAt_Ici_of_step {f g g' : ℝ → ℝ}
    (hpos : ∀ y, 1 ≤ y → f y = g y) (hneg : ∀ y, y < 1 → f y = 0)
    (hg : ∀ t, HasDerivAt g (g' t) t) (t : ℝ) :
    HasDerivWithinAt f (if 1 ≤ t then g' t else 0) (Ici t) t := by
  split_ifs with h
  · exact (hg t).hasDerivWithinAt.congr (fun y hy => hpos y (h.trans hy)) (hpos t h)
  · refine ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_).hasDerivWithinAt
    filter_upwards [Iio_mem_nhds (not_le.mp h)] with y hy
    exact hneg y hy

/-- The base joint's error after the step, as a function of time. -/
private lemma hasDerivAt_errFormula (c t : ℝ) :
    HasDerivAt (fun t : ℝ => c / 80 ^ 2 * (1 - (1 + 80 * (t - 1)) * Real.exp (-(80 * (t - 1)))))
      (c * (t - 1) * Real.exp (-(80 * (t - 1)))) t := by
  have h1 : HasDerivAt (fun t : ℝ => 80 * (t - 1)) 80 t := by
    simpa using ((hasDerivAt_id t).sub_const 1).const_mul 80
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (-(80 * (t - 1))))
      (Real.exp (-(80 * (t - 1))) * -80) t := h1.neg.exp
  have h3 : HasDerivAt (fun t : ℝ => (1 + 80 * (t - 1)) * Real.exp (-(80 * (t - 1))))
      (80 * Real.exp (-(80 * (t - 1))) + (1 + 80 * (t - 1)) * (Real.exp (-(80 * (t - 1))) * -80))
      t := (h1.const_add 1).mul h2
  exact ((h3.const_sub 1).const_mul (c / 80 ^ 2)).congr_deriv (by ring)

/-- The base joint's velocity after the step, as a function of time. -/
private lemma hasDerivAt_velFormula (c t : ℝ) :
    HasDerivAt (fun t : ℝ => c * (t - 1) * Real.exp (-(80 * (t - 1))))
      (c * (1 - 80 * (t - 1)) * Real.exp (-(80 * (t - 1)))) t := by
  have h1 : HasDerivAt (fun t : ℝ => 80 * (t - 1)) 80 t := by
    simpa using ((hasDerivAt_id t).sub_const 1).const_mul 80
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (-(80 * (t - 1))))
      (Real.exp (-(80 * (t - 1))) * -80) t := h1.neg.exp
  have h3 : HasDerivAt (fun t : ℝ => c * (t - 1)) c t := by
    simpa using ((hasDerivAt_id t).sub_const 1).const_mul c
  exact (h3.mul h2).congr_deriv (by ring)

/-- The right derivative of the base joint's error is its velocity. -/
private lemma stepErr_hasDerivWithinAt (c t : ℝ) :
    HasDerivWithinAt (fun t => stepErr c (t - 1)) (stepErrVel c (t - 1)) (Ici t) t := by
  have h := hasDerivWithinAt_Ici_of_step (f := fun t => stepErr c (t - 1))
    (fun y hy => by simp [stepErr, max_eq_left (sub_nonneg.mpr hy)])
    (fun y hy => by simp [stepErr, max_eq_right (sub_nonpos.mpr hy.le)])
    (hasDerivAt_errFormula c) t
  convert h using 1
  split_ifs with ht
  · simp [stepErrVel, max_eq_left (sub_nonneg.mpr ht)]
  · simp [stepErrVel, max_eq_right (sub_nonpos.mpr (not_le.mp ht).le)]

/-- The right derivative of the base joint's velocity is its acceleration from the right. -/
private lemma stepErrVel_hasDerivWithinAt (c t : ℝ) :
    HasDerivWithinAt (fun t => stepErrVel c (t - 1)) (stepErrAcc c (t - 1)) (Ici t) t := by
  have h := hasDerivWithinAt_Ici_of_step (f := fun t => stepErrVel c (t - 1))
    (fun y hy => by simp [stepErrVel, max_eq_left (sub_nonneg.mpr hy)])
    (fun y hy => by simp [stepErrVel, max_eq_right (sub_nonpos.mpr hy.le)])
    (hasDerivAt_velFormula c) t
  convert h using 1
  simp [stepErrAcc, sub_nonneg]

/-- The step response satisfies `ë = −160 ė − 6400 e + c` after the step and `0 = 0` before. -/
private lemma stepErr_ode (c t : ℝ) :
    stepErrAcc c (t - 1) =
      -(160 * stepErrVel c (t - 1)) - 6400 * stepErr c (t - 1) + (if 1 ≤ t then c else 0) := by
  by_cases ht : 1 ≤ t
  · simp only [stepErrAcc, stepErrVel, stepErr, max_eq_left (sub_nonneg.mpr ht),
      sub_nonneg.mpr ht, ↓reduceIte, ht]
    ring
  · simp only [stepErrAcc, stepErrVel, stepErr, max_eq_right (sub_nonpos.mpr (not_le.mp ht).le),
      ht, ↓reduceIte, show ¬ (0 ≤ t - 1) by linarith]
    simp

/-- The idle run is a timed run of the cell loop for every loop data and every motion: with no
request the idle supervisor waits at every boundary. A design statement, not from MLS. -/
theorem idle_isCellRun (L : Params 3 Waypoint) (x v : ℝ → Fin 3 → ℝ) :
    IsCellRun L Instances.params x v idleState idleActs := by
  exact ⟨rfl, fun _ => ⟨[], [], _, rfl, by simp, rfl, PolicyStep.wait _ rfl⟩⟩

/-- **The step run follows the rest reference at home with the acceleration from the right.**
For `0 ≤ c ≤ 192` and every time `t`, the step run meets `CellArmFollowsAccelRightAt` at the gain
`80` rad/s and the tube radius `3/100` rad for the rest move from home to home admitted at `0`:
right derivatives of the position and the velocity, `|(M(x)⁻¹ d)ᵢ| ≤ 192` rad/s² and the arm's
equations of motion under computed torque plus the step disturbance. A design statement, not from
MLS. -/
theorem stepMotion_follows_right {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 192) (t : ℝ) :
    CellArmFollowsAccelRightAt 80 2 (3 / 100) (stepMotion c) (stepVel c) (stepAcc c)
      (stepDist c) (DegPoint.toRad Instances.params.home) (DegPoint.toRad Instances.params.home)
      0 t := by
  set w : Fin 3 → ℝ := Pi.single 0 (if 1 ≤ t then c else 0) with hw
  refine ⟨?_, ?_, fun i => ?_, ?_⟩
  · refine hasDerivWithinAt_pi.2 fun i => ?_
    by_cases hi : i = 0
    · subst hi
      simpa [stepMotion, stepVel] using
        (stepErr_hasDerivWithinAt c t).const_add (DegPoint.toRad Instances.params.home 0)
    · simpa [stepMotion, stepVel, Pi.single_eq_of_ne hi] using
        (hasDerivWithinAt_const t (Ici t) (DegPoint.toRad Instances.params.home i))
  · refine hasDerivWithinAt_pi.2 fun i => ?_
    by_cases hi : i = 0
    · subst hi
      simpa [stepVel, stepAcc] using stepErrVel_hasDerivWithinAt c t
    · simpa [stepVel, stepAcc, Pi.single_eq_of_ne hi] using
        (hasDerivWithinAt_const t (Ici t) (0 : ℝ))
  · have h := Control.PosDef.inv_mulVec_mulVec (cellArm_M_posDef (stepMotion c t)) w
    change (cellRobot.M (stepMotion c t))⁻¹ *ᵥ (cellRobot.M (stepMotion c t) *ᵥ w) = w at h
    change |((cellRobot.M (stepMotion c t))⁻¹ *ᵥ (cellRobot.M (stepMotion c t) *ᵥ w)) i| ≤ _
    rw [h, hw]
    by_cases hi : i = 0
    · subst hi
      split_ifs <;> simp [abs_of_nonneg hc0] <;> linarith
    · simp [Pi.single_eq_of_ne hi]
      norm_num
  · have hacc : stepAcc c t = (0 - ((2 * 80 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ
        (stepVel c t - 0) - (((80 : ℝ) ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ
        (stepMotion c t - DegPoint.toRad Instances.params.home)) + w := by
      funext i
      by_cases hi : i = 0
      · subst hi
        simp only [stepAcc, stepVel, stepMotion, hw, Pi.add_apply, Pi.sub_apply, Pi.zero_apply,
          Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
          add_sub_cancel_left, sub_zero]
        rw [stepErr_ode]
        ring
      · simp [stepAcc, stepVel, stepMotion, hw, Pi.single_eq_of_ne hi, Matrix.one_apply_ne hi]
    simp only [Control.RobotSystem.computedTorque, Control.computedTorqueAlong, moveRef_self,
      moveRefDeriv_self, moveRefDeriv2_self, stepDist]
    rw [hacc, Matrix.mulVec_add, ← hw]
    abel

/-- The step run's position and velocity are continuous on `[0, ∞)`. A design statement, not
from MLS. -/
theorem step_continuousOn (c : ℝ) :
    ContinuousOn (fun s => (stepMotion c s, stepVel c s)) (Ici 0) := by
  have he : Continuous fun s => stepErr c (s - 1) := by
    unfold stepErr
    fun_prop
  have hv : Continuous fun s => stepErrVel c (s - 1) := by
    unfold stepErrVel
    fun_prop
  refine (Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun i => ?_)).continuousOn
  · by_cases hi : i = 0
    · subst hi
      simp only [stepMotion, Pi.add_apply, Pi.single_eq_same]
      exact continuous_const.add he
    · simpa [stepMotion, Pi.single_eq_of_ne hi] using continuous_const
  · by_cases hi : i = 0
    · subst hi
      simpa [stepVel] using hv
    · simpa [stepVel, Pi.single_eq_of_ne hi] using continuous_const

/-- The step run starts at home at rest, in the tube of radius `3/100` rad. A design statement,
not from MLS. -/
theorem step_inTube_zero (c : ℝ) :
    InTube (3 / 100) 80 (DegPoint.toRad Instances.params.home) 0 (stepMotion c 0)
      (stepVel c 0) := by
  intro i
  norm_num [stepMotion, stepVel, stepErr, stepErrVel]

/-- **A run whose acceleration jumps meets every hypothesis of the one-sided assured cell.** For
`0 ≤ c ≤ 192` rad/s², the idle run with the step disturbance at `t = 1` s meets every hypothesis
of `cell_assured_accel_design_tight_right`, so both links keep `9/100` m from every obstacle at
every `t ≥ 0` and the supervisor never faults and its age stays below 25. A design statement,
not from MLS. -/
theorem step_assured_tight_right {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 192) :
    (∀ t, 0 ≤ t → sceneClear (stepMotion c t)) ∧
    (∀ k, (idleState k).sup.faulted = false ∧ (idleState k).sup.age < 25) := by
  have htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelRightAt 80 2 (3 / 100) (stepMotion c) (stepVel c) (stepAcc c)
        (stepDist c) (DegPoint.toRad (idleState (k + 1)).src)
        (DegPoint.toRad (idleState (k + 1)).goal) ((idleState (k + 1)).start * (1 / 10)) t := by
    intro k t _
    simpa [idleState, CellState.init] using stepMotion_follows_right hc0 hc t
  obtain ⟨hclear, hfault, -, -⟩ := cell_assured_accel_design_tight_right (idle_isCellRun _ _ _)
    htrack (step_continuousOn c) (step_inTube_zero c)
  exact ⟨hclear, hfault⟩

/-- **The step run's velocity has no two-sided derivative at the step.** For `c > 0`, the
velocity `stepVel c` is not differentiable at `t = 1` s: its left derivative there is `0` and its
right derivative is `c` on the base joint. A design statement, not from MLS. -/
theorem stepVel_not_differentiableAt {c : ℝ} (hc : 0 < c) :
    ¬ DifferentiableAt ℝ (stepVel c) 1 := by
  intro h
  have hd := hasDerivAt_pi.1 h.hasDerivAt 0
  have hr : HasDerivWithinAt (fun t => stepVel c t 0) c (Ici 1) 1 := by
    simpa [stepVel, stepErrAcc] using stepErrVel_hasDerivWithinAt c 1
  have hl : HasDerivWithinAt (fun t => stepVel c t 0) 0 (Iic 1) 1 :=
    (hasDerivWithinAt_const 1 (Iic 1) (0 : ℝ)).congr_of_mem
      (fun y hy => by simp [stepVel, stepErrVel, max_eq_right (sub_nonpos.mpr (mem_Iic.mp hy))])
      (mem_Iic.2 le_rfl)
  have e1 := (uniqueDiffWithinAt_Ici 1).eq_deriv _ hd.hasDerivWithinAt hr
  have e2 := (uniqueDiffWithinAt_Iic 1).eq_deriv _ hd.hasDerivWithinAt hl
  linarith

/-- **The two-sided assured cell does not apply to the step run.** For `c > 0`, no acceleration
curve `acc` and no disturbance `d` make the per-period hypothesis of
`cell_assured_accel_design_tight` (the two-sided predicate `CellArmFollowsAccelAt`) hold for the
step run's position and velocity: it fails at `t = 1` s, in the period `(9/10, 1]`. A design
statement, not from MLS. -/
theorem step_not_followsAccelAt {c : ℝ} (hc : 0 < c) (acc d : ℝ → Fin 3 → ℝ) :
    ¬ ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelAt 80 2 (3 / 100) (stepMotion c) (stepVel c) acc d
        (DegPoint.toRad (idleState (k + 1)).src) (DegPoint.toRad (idleState (k + 1)).goal)
        ((idleState (k + 1)).start * (1 / 10)) t := by
  intro h
  exact stepVel_not_differentiableAt hc (h 9 1 ⟨by norm_num, by norm_num⟩).2.1.differentiableAt

end RoboLean.Cell.Loop
