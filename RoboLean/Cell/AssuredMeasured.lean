import RoboLean.Cell.LoopMeasured
import RoboLean.Cell.AssuredContract

/-!
# The assured cell on measured samples

The assured cell theorem of `RoboLean.Cell.AssuredContract` with the policy's decisions taken
from measured samples instead of the exact state at the boundaries. A timed run of the cell loop on
measured samples (`IsMeasuredCellRun`) sends at each boundary `k h` queue actions followed by the
policy's action on the measured sample `(xm k, vm k)`, each accepted by the supervisor. If every
sample is within `εq` (rad) of the true joint positions and within `εv` (rad/s) of the true joint
velocities, and the arrival tolerances leave room for these errors (`δ + εq ≤ δ_a`,
`2 ω δ + εv ≤ v_a`), the conclusions of `cell_assured_contract_right` hold for the true motion.
Every conclusion is about the true configuration `x`, never about a quantity computed from the
samples, so the tool bound at a finish is the same as for exact samples.

* `IsMeasuredCellRun`: the timed runs of the cell loop on measured samples;
  `IsCellRun.isMeasuredCellRun`: a run on the exact samples is one.
* `IsMeasuredCellRun.isMeasuredOpenRun`, `IsMeasuredCellRun.loopContract`: such a run is a measured
  run of the open loop whose states meet the loop-level contract, given the supervisor's contract.
* `cell_assured_measured_right`: the assured cell on measured samples.
* `cell_assured_measured_design_right`: at `h = 1/10` s, `T = 2` s, `ω = 80` rad/s,
  `δ = 3/100` rad, `δ_a = 7/4` degrees, `v_a = 5` rad/s, `εq = 1/2000` rad and `εv = 1/5` rad/s.

The arm is `cellArm` (MLS Example 4.3, printed p. 172, with the cell's parameters) under computed
torque (MLS eq. (4.49), p. 191), with the position and the velocity required to have right
derivatives only. These are design statements, not from MLS. They concern the ideal rigid-body
model with a bounded disturbance and the ideal sampled loop with a bounded sample error; they do
not assert that a closed-loop solution exists, and say nothing about how the samples are measured,
delay, actuator limits or a physical arm. Seconds, radians, radians per second; samples at the
boundaries `k h`.
-/

noncomputable section

namespace RoboLean.Cell.Loop

open Set Supervisor

/-- A timed run of the cell loop on measured samples: the loop states `c k` before the boundary
`k` start at `CellState.init p.home`, and the actions `acts k` sent at boundary `k` take `c k` to
`c (k + 1)` with the measured sample `(xm k, vm k)` (rad, rad/s) taken at the boundary `k h`. A
design model, not from MLS. -/
def IsMeasuredCellRun (L : Loop.Params 3 Waypoint) (p : Supervisor.Params)
    (xm vm : ℕ → Fin 3 → ℝ) (c : ℕ → CellState) (acts : ℕ → List Action) : Prop :=
  c 0 = CellState.init p.home ∧ ∀ k : ℕ, Boundary L p k (xm k) (vm k) (c k) (acts k) (c (k + 1))

/-- **The executable supervisor's state is the result of `run`, on measured samples.** Along a
timed run of the cell loop on measured samples, the supervisor's state before boundary `k` is
`Supervisor.run p (State.init p.home)` of all the actions sent before `k`. A design statement, not
from MLS. -/
theorem IsMeasuredCellRun.run_eq_apply {L : Loop.Params 3 Waypoint} {p : Supervisor.Params}
    {xm vm : ℕ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (h : IsMeasuredCellRun L p xm vm c acts) (k : ℕ) :
    run p (Supervisor.State.init p.home) (actsUpTo acts k) = some (c k).sup := by
  induction k with
  | zero => rw [h.1]; rfl
  | succ k ih =>
    rw [actsUpTo, run_append_apply, ih]
    exact (h.2 k).run_apply

/-- Along a timed run of the cell loop on measured samples, the commanded list is the controller's
goal while busy, by the effects of the accepted actions. A design statement, not from MLS. -/
theorem IsMeasuredCellRun.commanded_eq_apply {L : Loop.Params 3 Waypoint} {p : Supervisor.Params}
    {xm vm : ℕ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (h : IsMeasuredCellRun L p xm vm c acts) (k : ℕ) :
    (c k).sup.busy = true → (c k).sup.commanded = [(c k).goal] := by
  induction k with
  | zero => rw [h.1]; simp [CellState.init, Supervisor.State.init]
  | succ k ih => exact (h.2 k).commanded_eq_apply ih

/-- **A timed run of the cell loop on measured samples is a measured run of the open loop.** For
loop data whose bound is the supervisor's, the loop states form a timed run of the open loop from
`p.home` on the same measured samples; no guard of the supervisor is used. A design statement, not
from MLS. -/
theorem IsMeasuredCellRun.isMeasuredOpenRun {L : Loop.Params 3 Waypoint} {p : Supervisor.Params}
    {xm vm : ℕ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hbound : L.bound = p.bound) (h : IsMeasuredCellRun L p xm vm c acts) :
    IsMeasuredOpenRun L p.home xm vm (fun k => (c k).toLoop) :=
  ⟨by show (c 0).toLoop = _; rw [h.1]; rfl,
    fun k => (h.2 k).toOpenStep hbound (h.commanded_eq_apply k)⟩

/-- **The supervisor's contract gives the loop-level contract, on measured samples.** Along a
timed run of the cell loop on measured samples, for a supervisor whose runs meet the contract and
loop data whose link relation contains the program's link test, the loop states meet
`LoopContract`. A design statement, not from MLS. -/
theorem IsMeasuredCellRun.loopContract {L : Loop.Params 3 Waypoint} {p : Supervisor.Params}
    {xm vm : ℕ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hsup : Supervisor.Contract p)
    (hlink : ∀ a b, Supervisor.linked p.cells a b = true → L.linked a b)
    (h : IsMeasuredCellRun L p xm vm c acts) : LoopContract L (fun k => (c k).toLoop) :=
  fun k => by
    obtain ⟨-, -, -, -, h5, h6⟩ := hsup _ _ (h.run_eq_apply k)
    refine ⟨fun hb => hlink _ _ (h6 _ ?_), h5⟩
    rw [h.commanded_eq_apply k hb]
    exact List.mem_singleton_self _

/-- A timed run of the cell loop on the exact samples is a run on the measured samples
`(x (k h), v (k h))`. A design statement, not from MLS. -/
theorem IsCellRun.isMeasuredCellRun {L : Loop.Params 3 Waypoint} {p : Supervisor.Params}
    {x v : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (h : IsCellRun L p x v c acts) :
    IsMeasuredCellRun L p (fun k => x (k * L.period)) (fun k => v (k * L.period)) c acts :=
  ⟨h.1, h.2⟩

/-- The standing hypotheses of the loop on measured samples for the cell, from a timed run of the
executable supervisor on measured samples within `εq` (rad) and `εv` (rad/s) of the true state,
tracking of the last admitted move and the tube at home at time 0, for any tracking predicate
`follows` for which the move corollary holds. Seconds, radians, radians per second. A design
statement, not from MLS. -/
theorem cell_measured_hyps {h T δa va ω δ εq εv : ℝ} (hh : 0 < h) (hT : 0 < T)
    (hN : ⌈T / h⌉₊ ≤ 25) (hω : 0 ≤ ω) (hδa : δ + εq ≤ δa) (hva : 2 * ω * δ + εv ≤ va)
    {follows : Waypoint → Waypoint → ℝ → ℝ → Prop}
    {x v : ℝ → Fin 3 → ℝ} {xm vm : ℕ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsMeasuredCellRun (openCellParams h T δa va) Instances.params xm vm c acts)
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

/-- **The assured cell on measured samples.** For the cell's arm `cellArm` under computed torque
with the gains `ω² I`, `2ω I` (MLS eq. (4.49), p. 191, along a motion as on p. 301), the scene's
three cells and obstacles, and the executable cell supervisor with its instance cells and age
bound 25, whose runs are assumed to meet the contract `Supervisor.Contract Instances.params`
(`hsup`): let `0 < h`, `0 < T`, `⌈T/h⌉ ≤ 25`, `0 < ω`, `δ ≤ 1/20`, `δ + εq ≤ δ_a`,
`2 ω δ + εv ≤ v_a` (seconds, radians, radians per second). Then for every timed run `c` of the cell
loop on measured samples `(xm, vm)` with the actions `acts` sent to the supervisor and every motion
`(x, v, acc)` with disturbance torque `d`, under the hypotheses
* (harness, `hrun`) at each boundary `k h` the actions sent are queue actions followed by the
  policy's action on the measured sample `(xm k, vm k)`, each accepted by the supervisor;
* (sensing, `hsamp`) every measured sample is within `εq` of the true joint positions `x (k h)` and
  within `εv` of the true joint velocities `v (k h)`, in every joint;
* (harness and plant, `htrack`) at every instant `t` of each period `(k h, (k + 1) h]` the arm
  obeys its equations of motion `M ẍ + C ẋ + N = F + d` with the computed torque `F` tracking the
  quintic reference of the last admitted move, `x` and `v` have the right derivatives `v t` and
  `acc t`, and `|(M(x)⁻¹ d)ᵢ| ≤ ω² δ` for every joint;
* (plant, `hcont`) `(x, v)` is continuous on `[0, ∞)`;
* (harness, `h0`) the arm starts in the tube around home at rest,
the conclusions are those of `cell_assured_contract_right`, all about the true motion: the
supervisor's state before boundary `k` is `Supervisor.run` of the actions sent so far; every point
of both links keeps a Euclidean distance of at least `9/100` m from every obstacle at every
`t ≥ 0`; the supervisor never faults and its age stays below 25; a move admitted at boundary `k₀`
is busy until and finished at boundary `k₀ + ⌈T/h⌉`, with the arm at its goal; at each finish the
arm is in the tube around the goal at rest and the tool at the true configuration is within
`(73/50) δ` m of the goal's tool position. A design statement, not from MLS. -/
theorem cell_assured_measured_right {h T δa va ω δ εq εv : ℝ} (hh : 0 < h) (hT : 0 < T)
    (hN : ⌈T / h⌉₊ ≤ 25) (hω : 0 < ω) (hδa : δ + εq ≤ δa) (hva : 2 * ω * δ + εv ≤ va)
    (hδ : δ ≤ 1 / 20) (hsup : Supervisor.Contract Instances.params)
    {x v acc d : ℝ → Fin 3 → ℝ} {xm vm : ℕ → Fin 3 → ℝ} {c : ℕ → CellState}
    {acts : ℕ → List Action}
    (hrun : IsMeasuredCellRun (openCellParams h T δa va) Instances.params xm vm c acts)
    (hsamp : ∀ k : ℕ, ∀ i : Fin 3, |xm k i - x (k * h) i| ≤ εq ∧ |vm k i - v (k * h) i| ≤ εv)
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
  have H := cell_measured_hyps hh hT hN hω.le hδa hva hrun hsamp htrack
    (cellArm_moveCorollary_accel_right (openCellParams h T δa va) hT hω hcont) h0
  have hc := hrun.loopContract hsup (fun _ _ hab => hab)
  obtain ⟨hclear, hfault, hfin, htool, htube⟩ :=
    H.assured hc (openCellParams_certify h T δa va) hδ sceneTool_lipschitz
  refine ⟨hrun.run_eq_apply, hclear, hfault, fun k₀ hidle hbusy => ?_, fun k hbusy hidle => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hfin k₀ hidle hbusy
    exact ⟨hrun.commanded_eq_apply _ hbusy, h1, h2, h3⟩
  · obtain ⟨h1, h2⟩ := htube k hbusy hidle
    exact ⟨hrun.commanded_eq_apply _ hbusy, h1, h2, htool k hbusy hidle⟩

/-- The design point's position tolerance `7/4` degrees, in radians, leaves room for the tube
radius `3/100` rad and the position sample error `1/2000` rad: `3/100 + 1/2000 ≤ 7π/720`, from
`π > 3.14`. A design statement, not from MLS. -/
theorem design_radius_add_le_posTol : (3 : ℝ) / 100 + 1 / 2000 ≤ degToRad (7 / 4) := by
  have := Real.pi_gt_d2
  unfold degToRad
  push_cast
  linarith

/-- **The assured cell on measured samples at the design point.** With `h = 1/10` s, `T = 2` s,
`ω = 80` rad/s, `δ = 3/100` rad, the position tolerance `δ_a = 7/4` degrees (`7π/720` rad), the
speed tolerance `v_a = 5` rad/s, and samples within `εq = 1/2000` rad and `εv = 1/5` rad/s of the
true state, and `|(M(x)⁻¹ d)ᵢ| ≤ 192` rad/s² for every joint, with the position and the velocity
required to have right derivatives only (`CellArmFollowsAccelRightAt`), for every run of the
supervisor that meets the contract `Supervisor.Contract Instances.params` (`hsup`): the links keep
`9/100` m from every obstacle at every `t ≥ 0`, the supervisor never faults and its age stays below
25, a move admitted at boundary `k₀` is finished at boundary `k₀ + 20`, and at each finish the
tool at the true configuration is within `219/5000` m of the goal's tool position. The other
hypotheses are those of `cell_assured_measured_right`: about the harness, that at each boundary the
actions sent are queue actions followed by the policy's action on the measured sample, each
accepted by the supervisor (`hrun`), and that the arm starts in the tube around home at rest
(`h0`); about sensing, the sample error bound (`hsamp`); about the harness and the plant, that on
each period the arm obeys its equations of motion with the computed torque tracking the quintic
reference of the last admitted move, with the acceleration from the right, and the disturbance
bound above (`htrack`); about the plant, that `(x, v)` is continuous on `[0, ∞)` (`hcont`). A
design statement, not from MLS. -/
theorem cell_assured_measured_design_right (hsup : Supervisor.Contract Instances.params)
    {x v acc d : ℝ → Fin 3 → ℝ} {xm vm : ℕ → Fin 3 → ℝ} {c : ℕ → CellState}
    {acts : ℕ → List Action}
    (hrun : IsMeasuredCellRun (openCellParams (1 / 10) 2 (degToRad (7 / 4)) 5) Instances.params
      xm vm c acts)
    (hsamp : ∀ k : ℕ, ∀ i : Fin 3, |xm k i - x (k * (1 / 10)) i| ≤ 1 / 2000 ∧
      |vm k i - v (k * (1 / 10)) i| ≤ 1 / 5)
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
    cell_assured_measured_right (ω := 80) (δ := 3 / 100) (εq := 1 / 2000) (εv := 1 / 5)
      (by norm_num) (by norm_num) (by rw [design_steps]; norm_num) (by norm_num)
      design_radius_add_le_posTol (by norm_num) (by norm_num) hsup hrun hsamp htrack hcont h0
  refine ⟨hclear, hfault, fun k₀ hidle hbusy => ?_, fun k hbusy hidle => ?_⟩
  · obtain ⟨-, -, h2, h3⟩ := hfin k₀ hidle hbusy
    rw [design_steps] at h2 h3
    exact ⟨h2, h3⟩
  · obtain ⟨-, -, -, h4⟩ := htool k hbusy hidle
    linarith

end RoboLean.Cell.Loop
