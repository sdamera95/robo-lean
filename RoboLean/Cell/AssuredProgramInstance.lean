import RoboLean.Cell.AssuredProgram
import RoboLean.Cell.AssuredInstanceRightStep

/-!
# A run of the program on encoder samples that meets every hypothesis

A satisfying instance of `cell_assured_program_measured_design`: the policy program at the design
configuration, run on samples read from the true state of the step run of
`RoboLean.Cell.AssuredInstanceRightStep` (the arm holds home, and a step disturbance of
`0 ≤ c ≤ 192` rad/s² on the base joint switches on at `t = 1` s), meets every hypothesis of the
theorem, so its conclusions hold for it.

* `encoderSample`: the sample at boundary `k`: each joint angle read by an encoder of `2^18` counts
  per revolution to the nearest count, and each joint speed floored to a multiple of `1/5` rad/s.
* `encoderSample_within`: such a sample is within `1/2000` rad and `1/5` rad/s of the true state.
* `idleProgram`, `idleProgram_isProgramRun`: with no request the program stays in its initial state
  and sends nothing, on every stream of samples.
* `program_step_assured`: the conclusions of `cell_assured_program_measured_design` for this run,
  with the supervisor's contract as a premise.

A design statement, not from MLS (the arm is `cellArm`, MLS Example 4.3, printed p. 172, under
computed torque, MLS eq. (4.49), p. 191). Seconds, radians, radians per second, radians per second
squared; samples at the boundaries `k/10` s. The run says nothing about real encoders, speed
estimators or the disturbances a real arm meets.
-/

noncomputable section

namespace RoboLean.Cell.Loop

open Set Supervisor

/-- The sample of the true state `(x, v)` at boundary `k` (time `k/10` s): for each joint `i`, the
encoder count `round (x (k/10) i · 2^18 / (2π))` (an encoder of `2^18` counts per revolution read
to the nearest count; `x` in radians) and the speed estimate `⌊5 · v (k/10) i⌋ / 5` (the true
speed in rad/s floored to a multiple of `1/5` rad/s). A design definition, not from MLS. -/
def encoderSample (x v : ℝ → Fin 3 → ℝ) (k : ℕ) : Policy.Sample where
  counts := (round (x (k * (1 / 10)) 0 * 2 ^ 18 / (2 * Real.pi)),
    round (x (k * (1 / 10)) 1 * 2 ^ 18 / (2 * Real.pi)),
    round (x (k * (1 / 10)) 2 * 2 ^ 18 / (2 * Real.pi)))
  vel := (((⌊5 * v (k * (1 / 10)) 0⌋ : ℤ) : ℚ) / 5, ((⌊5 * v (k * (1 / 10)) 1⌋ : ℤ) : ℚ) / 5,
    ((⌊5 * v (k * (1 / 10)) 2⌋ : ℤ) : ℚ) / 5)

/-- An angle `θ` (rad) read by an encoder of `2^18` counts per revolution to the nearest count, and
the count read back in radians through degrees, is within `π/2^18 < 1/2000` rad of `θ`. A design
statement, not from MLS. -/
theorem abs_degToRad_countsToDeg_round_sub_le (θ : ℝ) :
    |degToRad (Policy.countsToDeg (2 ^ 18) (round (θ * 2 ^ 18 / (2 * Real.pi)))) - θ| ≤
      1 / 2000 := by
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_le_four
  set y := θ * 2 ^ 18 / (2 * Real.pi) with hy
  have hθ : θ = y * (2 * Real.pi / 2 ^ 18) := by
    rw [hy]
    field_simp
  have hr := abs_sub_round y
  have e : degToRad (Policy.countsToDeg (2 ^ 18) (round y)) - θ =
      ((round y : ℝ) - y) * (2 * Real.pi / 2 ^ 18) := by
    rw [hθ]
    unfold degToRad Policy.countsToDeg
    push_cast
    ring
  have hpos : (0 : ℝ) < 2 * Real.pi / 2 ^ 18 := by positivity
  rw [e, abs_mul, abs_of_pos hpos, abs_sub_comm]
  calc |y - (round y : ℝ)| * (2 * Real.pi / 2 ^ 18) ≤ 1 / 2 * (2 * Real.pi / 2 ^ 18) :=
        mul_le_mul_of_nonneg_right hr (by positivity)
    _ ≤ 1 / 2000 := by linarith

/-- A speed `w` (rad/s) floored to a multiple of `1/5` rad/s is within `1/5` rad/s of `w`. A design
statement, not from MLS. -/
theorem abs_floor_div_five_sub_le (w : ℝ) :
    |((((⌊5 * w⌋ : ℤ) : ℚ) / 5 : ℚ) : ℝ) - w| ≤ 1 / 5 := by
  have h1 := Int.floor_le (5 * w)
  have h2 := Int.lt_floor_add_one (5 * w)
  push_cast
  rw [abs_le]
  constructor <;> linarith

/-- **The encoder sample is within the design's sample error.** At every boundary `k` and joint
`i`, the angle of `encoderSample x v k` read in radians at the design configuration (`2^18` counts
per revolution) is within `1/2000` rad of `x (k/10) i`, and its speed estimate is within `1/5`
rad/s of `v (k/10) i`. A design statement, not from MLS. -/
theorem encoderSample_within (x v : ℝ → Fin 3 → ℝ) (k : ℕ) (i : Fin 3) :
    |(encoderSample x v k).toRad Policy.design i - x (k * (1 / 10)) i| ≤ 1 / 2000 ∧
      |(encoderSample x v k).velRad i - v (k * (1 / 10)) i| ≤ 1 / 5 := by
  fin_cases i
  · exact ⟨abs_degToRad_countsToDeg_round_sub_le (x (k * (1 / 10)) 0),
      abs_floor_div_five_sub_le (v (k * (1 / 10)) 0)⟩
  · exact ⟨abs_degToRad_countsToDeg_round_sub_le (x (k * (1 / 10)) 1),
      abs_floor_div_five_sub_le (v (k * (1 / 10)) 1)⟩
  · exact ⟨abs_degToRad_countsToDeg_round_sub_le (x (k * (1 / 10)) 2),
      abs_floor_div_five_sub_le (v (k * (1 / 10)) 2)⟩

/-- The states of the idle program: the program's initial state at the design configuration at
every boundary. A design definition, not from MLS. -/
def idleProgram : ℕ → Policy.State := fun _ => Policy.State.init Policy.design

/-- **With no request the program stays idle.** On every stream of samples and no request, the
program at the design configuration sends nothing and keeps its initial state at every boundary.
A design statement, not from MLS. -/
theorem idleProgram_isProgramRun (smp : ℕ → Policy.Sample) :
    Policy.IsProgramRun Policy.design (fun _ => []) smp idleProgram (fun _ => []) :=
  ⟨rfl, fun _ => rfl⟩

/-- **The program on encoder samples of the step run meets every hypothesis.** For a supervisor
whose runs meet the contract (`hsup`) and `0 ≤ c ≤ 192` rad/s², the idle program at the design
configuration, run on the encoder samples of the step run (the arm holding home, with a step
disturbance producing the acceleration `c` on the base joint from `t = 1` s), meets every
hypothesis of `cell_assured_program_measured_design`; hence both links keep `9/100` m from every
obstacle at every `t ≥ 0`, the supervisor never faults and its age stays below 25, and the
statements about admissions and finishes hold (vacuously here, since nothing is admitted). A
design statement, not from MLS. -/
theorem program_step_assured (hsup : Supervisor.Contract Instances.params) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c ≤ 192) :
    (∀ t, 0 ≤ t → sceneClear (stepMotion c t)) ∧
    (∀ k, (idleProgram k).sup.faulted = false ∧ (idleProgram k).sup.age < 25) ∧
    (∀ k₀, (idleProgram k₀).sup.busy = false → (idleProgram (k₀ + 1)).sup.busy = true →
      (idleProgram (k₀ + 20 + 1)).sup.busy = false ∧
        (idleProgram (k₀ + 20 + 1)).sup.current = (idleProgram (k₀ + 1)).goal) ∧
    (∀ k, (idleProgram k).sup.busy = true → (idleProgram (k + 1)).sup.busy = false →
      dist (sceneTool (stepMotion c (k * (1 / 10))))
        (sceneTool (DegPoint.toRad (idleProgram k).goal)) ≤ 219 / 5000) := by
  have htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelRightAt 80 2 (3 / 100) (stepMotion c) (stepVel c) (stepAcc c)
        (stepDist c) (DegPoint.toRad (idleProgram (k + 1)).src)
        (DegPoint.toRad (idleProgram (k + 1)).goal) ((idleProgram (k + 1)).start * (1 / 10)) t := by
    intro k t _
    simpa [idleProgram, Policy.State.init, Policy.design] using stepMotion_follows_right hc0 hc t
  exact cell_assured_program_measured_design hsup
    (idleProgram_isProgramRun (encoderSample (stepMotion c) (stepVel c)))
    (encoderSample_within (stepMotion c) (stepVel c)) htrack (step_continuousOn c)
    (step_inTube_zero c)

end RoboLean.Cell.Loop
