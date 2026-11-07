import RoboLean.Cell.AssuredNominalGain50

/-!
# The assured cell at the gain 50 with a payload that changes from move to move

The program-form theorem `cell_assured_program_nominal_gain50` fixes one nominal mass `mn` in the
controller's model, one actual mass `m` in the plant and one pair of friction levels for the whole
run. In a pick-and-place cycle the part's mass enters the plant at the pick and leaves it at the
place, and the controller's model carries the nominal mass only while the part is carried: the
pair of masses is `(mn, m)` on some moves and `(0, 0)` on others. This file states the theorem with
the masses and the friction levels changing along the run, under the same side conditions at
every instant: the rotor inertias `J`, `J'`, the error bounds `dm`, `dJ` stay common.

**Formalized.**

* `Loop.cellArm_moveCorollary_nominal_gain50_varying`: the loop's move corollary at `(50, 3/100)`
  with the masses and the friction levels functions of time.
* `Loop.cell_assured_program_nominal_gain50_varying`: the conclusions of
  `cell_assured_program_nominal_gain50` with the masses and the friction levels functions of time.
* `Loop.cell_assured_program_nominal_gain50_switch`: the same with values indexed by the period.
* `Loop.cell_assured_program_nominal_gain50_switch_exact`: the same for samples equal to the true
  state.
* `Loop.program_hold_switch_nominal_gain50_assured`: the idle program on encoder samples of the
  arm at rest at home, with no part on the first period and a mass error of `1` kg held by
  friction after, meets every hypothesis of `cell_assured_program_nominal_gain50_switch`.

The bound on the disturbance (`cellLoaded_accel_abs_le_gain50`) is a statement about one instant:
its hypotheses and its conclusion involve the configuration, the speed, the commanded acceleration,
the friction torque and the parameters at that instant only, so the masses and the friction levels
may change from one instant to the next. The tube argument
(`tube_invariant_on_accel_right_of_inTube`) takes the controller's model as a function of time.

Computed torque of MLS eq. (4.49), p. 191, for the robot of p. 303; the plant's equations, MLS
eq. (4.47), p. 190, with friction as a joint force, p. 170. Lean joint `k` is the book's joint
`k + 1`; radians, seconds, kg, kg m², N m. The arm's numbers, the rotor model, the payload's
location, the friction model, the scene, the loop, the configuration and the bounds are design
statements, not from MLS. Nothing here concerns a physical arm, and the compiled program only
through the Lean definitions it is built from.
-/

noncomputable section

open Matrix Set

namespace RoboLean
namespace Cell.Loop

open Set Supervisor

/-- **The loop's move corollary at the gain 50 with the masses and the friction levels changing in
time (a design statement, not from MLS; computed torque of MLS eq. (4.49), p. 191, for the robot of
p. 303; the plant's equations, MLS eq. (4.47), p. 190, with friction as a joint force, p. 170).**
At the gain `ω = 50` rad/s, tube radius `δ = 3/100` rad and move duration `T = 2` s, for the loop
data `openCellParams h 2 δa va`, let the controller's model carry the rotor inertia `J` (kg m²) on
every joint and the nominal mass `mn t ≥ 0` (kg) at time `t`, and the plant the rotor inertia
`J' ≥ 3/2` kg m² on every joint and the actual mass `m t ≥ 0` (kg), under the friction levels
`f_c t, f_v t ≥ 0` (N m, N m s), with `|m t − mn t| ≤ dm`, `|J' − J| ≤ dJ` and
`dm + (7/2) dJ + (f_c t + 4 f_v t)/60 ≤ 3/2` at every `t`. If `(x, v)` is continuous on `[0, ∞)`,
the arm's motion satisfies `Loop.MoveCorollary` for the quintic reference and the tracking
predicate `CellArmFollowsNominalRightAt` at the gain 50 taken at each instant `t` with the values
at `t`. The bound on the disturbance is used at each instant with that instant's values, and only
while the motion is in the tube of radius `301/10000` rad, which it never leaves (first exit). -/
theorem cellArm_moveCorollary_nominal_gain50_varying {J J' dm dJ : ℝ} {mn m fc fv : ℝ → ℝ}
    (hmn : ∀ t, 0 ≤ mn t) (hm : ∀ t, 0 ≤ m t) (hJ' : 3 / 2 ≤ J')
    (hdm : ∀ t, |m t - mn t| ≤ dm) (hdJ : |J' - J| ≤ dJ) (hfc : ∀ t, 0 ≤ fc t)
    (hfv : ∀ t, 0 ≤ fv t) (hcond : ∀ t, dm + 7 / 2 * dJ + (fc t + 4 * fv t) / 60 ≤ 3 / 2)
    (h δa va : ℝ) {x v acc f : ℝ → Fin 3 → ℝ} (hc : ContinuousOn (fun s => (x s, v s)) (Ici 0)) :
    MoveCorollary (openCellParams h 2 δa va) (quinticMoveRef (n := 3) (by norm_num : (0 : ℝ) < 2))
      (3 / 100) 50
      (fun a g t₀ t => CellArmFollowsNominalRightAt 50 2 J (mn t) J' (m t) (fc t) (fv t) x v acc
        f (DegPoint.toRad a) (DegPoint.toRad g) t₀ t) x v := by
  intro a g hag t₀ t₁ ht₀ _ hf hin t ht
  have hin' : Cell.InTube 50 (3 / 100) (x t₀) (v t₀)
      (moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 t₀)
      (moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 t₀) := by
    rw [moveRef_of_le (by norm_num) le_rfl, moveRefDeriv_of_le (by norm_num) le_rfl]
    exact hin
  have htube := tube_invariant_on_accel_right_of_inTube (η := 301 / 10000)
    (by norm_num : (0 : ℝ) < 50) (by norm_num : (3 : ℝ) / 100 < 301 / 10000)
    (hasDerivAt_moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2)
    (hasDerivAt_moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2)
    (Mt := fun s => (cellLoadedRobot J (mn s)).M (x s))
    (Ct := fun s => (cellLoadedRobot J (mn s)).C (x s) (v s))
    (Nt := fun s => (cellLoadedRobot J (mn s)).N (x s) (v s))
    (d := fun s => nominalDisturbance J (mn s) J' (m s) (x s) (v s) (acc s) (f s))
    (hc.mono fun s hs => ht₀.trans hs.1) (fun s hs => (hf s hs).1) (fun s hs => (hf s hs).2.1)
    (fun s hs hnear w hMw i => ?_) (fun s hs => (hf s hs).equations) hin'
  · exact (htube t ht).1
  · have := CellArmFollowsNominalRightAt.accel_bound_gain50 (hmn s) (hm s) hJ' (hdm s) hdJ
      (hfc s) (hfv s) (hcond s) hag (hf s hs) hnear w hMw i
    norm_num
    linarith

/-- **The assured cell at the gain 50 with every decision taken by the program, on measured
samples, with the masses and the friction levels changing in time (a design statement, not from
MLS; computed torque of MLS eq. (4.49), p. 191, for the robot of p. 303; the plant's equations,
MLS eq. (4.47), p. 190, with friction as a joint force, p. 170).** For every run of the policy
program at the configuration `Policy.designNominalGain50` (`hprog`), and every supervisor whose
runs meet the contract (`hsup`): let the controller's model carry the rotor inertia `J` (kg m²) on
every joint and, at time `t`, the nominal mass `mn t ≥ 0` (kg) at the tool point, and the plant the
rotor inertia `J' ≥ 3/2` kg m² on every joint and the actual mass `m t ≥ 0` (kg), under the
friction levels `f_c t, f_v t ≥ 0` (N m, N m s), with `|m t − mn t| ≤ dm`, `|J' − J| ≤ dJ` and
`dm + (7/2) dJ + (f_c t + 4 f_v t)/60 ≤ 3/2` at every `t`; the unknown is the mass error, the
rotor-inertia error and the friction, and the elasticity of the drives is not in the theorem's
plant. If at every boundary `k/10` s each joint angle of the sample, read in radians, is within
`1/50` rad of the true joint angle and each joint speed estimate is within `3/10` rad/s of the true
joint speed (`hsamp`), and under `htrack` (at every instant `t` of each period the plant, with the
masses and the friction levels at `t`, obeys its equations of motion under a friction torque `f`
with the computed torque of the controller's model tracking the quintic reference of the program's
last admitted move at the gain `50` rad/s, with right derivatives), `hcont` and `h0`: the links
keep `9/100` m from every obstacle at every `t ≥ 0`; the supervisor never faults and its age stays
below 25; a move admitted at boundary `k₀` keeps the supervisor busy at the boundaries
`k₀ + 1, …, k₀ + 20` and is finished at boundary `k₀ + 20` with the arm at its goal; and at each
finish the tool is within `219/5000` m of the goal's tool position.

A pick-and-place cycle, with the part's mass switched in the plant and in the controller's model
at the pick and at the place, is a run of this form with the values after the switch taken from the
switching instant `t_s` on (at a pick, `mn t = 0` and `m t = 0` for `t < t_s`, the nominal and the
actual part mass for `t ≥ t_s`): those are the values under which the plant hypothesis takes the
right derivatives at `t_s`. -/
theorem cell_assured_program_nominal_gain50_varying (hsup : Supervisor.Contract Instances.params)
    {reqs : ℕ → List Waypoint} {smp : ℕ → Policy.Sample} {st : ℕ → Policy.State}
    {acts : ℕ → List Action}
    (hprog : Policy.IsProgramRun Policy.designNominalGain50 reqs smp st acts)
    {J J' dm dJ : ℝ} {mn m fc fv : ℝ → ℝ} (hmn : ∀ t, 0 ≤ mn t) (hm : ∀ t, 0 ≤ m t)
    (hJ' : 3 / 2 ≤ J') (hdm : ∀ t, |m t - mn t| ≤ dm) (hdJ : |J' - J| ≤ dJ)
    (hfc : ∀ t, 0 ≤ fc t) (hfv : ∀ t, 0 ≤ fv t)
    (hcond : ∀ t, dm + 7 / 2 * dJ + (fc t + 4 * fv t) / 60 ≤ 3 / 2)
    {x v acc f : ℝ → Fin 3 → ℝ}
    (hsamp : ∀ k : ℕ, ∀ i : Fin 3,
      |(smp k).toRad Policy.designNominalGain50 i - x (k * (1 / 10)) i| ≤ 1 / 50 ∧
        |(smp k).velRad i - v (k * (1 / 10)) i| ≤ 3 / 10)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsNominalRightAt 50 2 J (mn t) J' (m t) (fc t) (fv t) x v acc f
        (DegPoint.toRad (st (k + 1)).src) (DegPoint.toRad (st (k + 1)).goal)
        ((st (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 50 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (st k).sup.faulted = false ∧ (st k).sup.age < 25) ∧
    (∀ k₀, (st k₀).sup.busy = false → (st (k₀ + 1)).sup.busy = true →
      (∀ j, j < 20 → (st (k₀ + 1 + j)).sup.busy = true) ∧
      (st (k₀ + 20 + 1)).sup.busy = false ∧ (st (k₀ + 20 + 1)).sup.current = (st (k₀ + 1)).goal) ∧
    (∀ k, (st k).sup.busy = true → (st (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (st k).goal)) ≤
        219 / 5000) := by
  have hrun : IsMeasuredCellRun (openCellParams (1 / 10) 2 (degToRad 3) (33 / 10)) Instances.params
      (fun k => (smp k).toRad Policy.designNominalGain50) (fun k => (smp k).velRad)
      (fun k => (st k).toCell) acts := by
    have h := hprog.isMeasuredCellRun
    rw [designNominalGain50_loop] at h
    exact h
  have hδa : (3 : ℝ) / 100 + 1 / 50 ≤ degToRad 3 := by
    have := Real.pi_gt_three
    unfold degToRad
    push_cast
    linarith
  have H := cell_measured_hyps (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 2)
    (by rw [design_steps]; norm_num) (by norm_num : (0 : ℝ) ≤ 50) hδa (by norm_num) hrun hsamp
    htrack
    (cellArm_moveCorollary_nominal_gain50_varying hmn hm hJ' hdm hdJ hfc hfv hcond (1 / 10)
      (degToRad 3) (33 / 10) hcont) h0
  have hc := hrun.loopContract hsup (fun _ _ hab => hab)
  obtain ⟨hclear, hfault, hfin, htool, -⟩ :=
    H.assured hc (openCellParams_certify (1 / 10) 2 (degToRad 3) (33 / 10))
      (by norm_num [cellInflation]) sceneTool_lipschitz
  refine ⟨hclear, hfault, fun k₀ hidle hbusy => ?_, fun k hbusy hidle => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hfin k₀ hidle hbusy
    have h1' : ∀ j, j < ⌈(2 : ℝ) / (1 / 10)⌉₊ → (st (k₀ + 1 + j)).sup.busy = true := h1
    have h2' : (st (k₀ + ⌈(2 : ℝ) / (1 / 10)⌉₊ + 1)).sup.busy = false := h2
    have h3' : (st (k₀ + ⌈(2 : ℝ) / (1 / 10)⌉₊ + 1)).sup.current = (st (k₀ + 1)).goal := h3
    rw [design_steps] at h1' h2' h3'
    exact ⟨h1', h2', h3'⟩
  · have h4 : dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (st k).goal)) ≤
        73 / 50 * (3 / 100) := htool k hbusy hidle
    linarith

/-- The index of the period `(k/10, (k+1)/10]` (s) that contains `t`: `⌈10 t⌉ − 1 = k`. -/
private theorem period_index {k : ℕ} {t : ℝ}
    (ht : t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10))) : ⌈t * 10⌉₊ - 1 = k := by
  have h : ⌈t * 10⌉₊ = k + 1 := by
    rw [Nat.ceil_eq_iff (by omega), Nat.add_sub_cancel]
    push_cast
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  omega

/-- **The assured cell at the gain 50 with every decision taken by the program, on measured
samples, with the masses and the friction levels changing from period to period (a design
statement, not from MLS; computed torque of MLS eq. (4.49), p. 191, for the robot of p. 303; the
plant's equations, MLS eq. (4.47), p. 190, with friction as a joint force, p. 170).** For every run
of the policy program at the configuration `Policy.designNominalGain50` (`hprog`), and every
supervisor whose runs meet the contract (`hsup`): let the controller's model carry the rotor
inertia `J` (kg m²) on every joint and, on the period `(k/10, (k+1)/10]` (s), the nominal mass
`mn k ≥ 0` (kg) at the tool point, and the plant the rotor inertia `J' ≥ 3/2` kg m² on every joint
and the actual mass `m k ≥ 0` (kg), under the friction levels `f_c k, f_v k ≥ 0` (N m, N m s), with
`|m k − mn k| ≤ dm`, `|J' − J| ≤ dJ` and `dm + (7/2) dJ + (f_c k + 4 f_v k)/60 ≤ 3/2` for every
period `k`; the unknown is the mass error, the rotor-inertia error and the friction, and the
elasticity of the drives is not in the theorem's plant. Under `hsamp` (samples within `1/50` rad
and `3/10` rad/s of the true state at every boundary `k/10` s), `htrack` (on the period `k` the
plant with that period's masses and friction levels obeys its equations of motion under a friction
torque `f` with the computed torque of the controller's model tracking the quintic reference of
the program's last admitted move at the gain `50` rad/s, with right derivatives), `hcont` and `h0`,
the conclusions are those of `cell_assured_program_nominal_gain50`: the links keep `9/100` m from
every obstacle at every `t ≥ 0`; the supervisor never faults and its age stays below 25; a move
admitted at boundary `k₀` keeps the supervisor busy at the boundaries `k₀ + 1, …, k₀ + 20` and is
finished at boundary `k₀ + 20` with the arm at its goal; and at each finish the tool is within
`219/5000` m of the goal's tool position.

The instance is the pick-and-place cycle, the part's mass in the plant and in the controller's
model switched at the pick and at the place: `(mn k, m k)` is `(mn, m)` on the carrying periods and
`(0, 0)` on the others. A period's values hold up to and including its closing boundary, where the
plant hypothesis takes the right derivative of the speed; after a switch at that boundary this is
the acceleration under the new masses, so the closing period's equation has to hold with it and a
friction torque within the closing period's bound, as it does for an arm held at rest by friction.
Where it does not, `cell_assured_program_nominal_gain50_varying`, with the values after the switch
taken from the boundary on, is the form to use. Proved from
`cell_assured_program_nominal_gain50_varying` with the values of the period that contains each
instant. -/
theorem cell_assured_program_nominal_gain50_switch (hsup : Supervisor.Contract Instances.params)
    {reqs : ℕ → List Waypoint} {smp : ℕ → Policy.Sample} {st : ℕ → Policy.State}
    {acts : ℕ → List Action}
    (hprog : Policy.IsProgramRun Policy.designNominalGain50 reqs smp st acts)
    {J J' dm dJ : ℝ} {mn m fc fv : ℕ → ℝ} (hmn : ∀ k, 0 ≤ mn k) (hm : ∀ k, 0 ≤ m k)
    (hJ' : 3 / 2 ≤ J') (hdm : ∀ k, |m k - mn k| ≤ dm) (hdJ : |J' - J| ≤ dJ)
    (hfc : ∀ k, 0 ≤ fc k) (hfv : ∀ k, 0 ≤ fv k)
    (hcond : ∀ k, dm + 7 / 2 * dJ + (fc k + 4 * fv k) / 60 ≤ 3 / 2)
    {x v acc f : ℝ → Fin 3 → ℝ}
    (hsamp : ∀ k : ℕ, ∀ i : Fin 3,
      |(smp k).toRad Policy.designNominalGain50 i - x (k * (1 / 10)) i| ≤ 1 / 50 ∧
        |(smp k).velRad i - v (k * (1 / 10)) i| ≤ 3 / 10)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsNominalRightAt 50 2 J (mn k) J' (m k) (fc k) (fv k) x v acc f
        (DegPoint.toRad (st (k + 1)).src) (DegPoint.toRad (st (k + 1)).goal)
        ((st (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 50 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (st k).sup.faulted = false ∧ (st k).sup.age < 25) ∧
    (∀ k₀, (st k₀).sup.busy = false → (st (k₀ + 1)).sup.busy = true →
      (∀ j, j < 20 → (st (k₀ + 1 + j)).sup.busy = true) ∧
      (st (k₀ + 20 + 1)).sup.busy = false ∧ (st (k₀ + 20 + 1)).sup.current = (st (k₀ + 1)).goal) ∧
    (∀ k, (st k).sup.busy = true → (st (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (st k).goal)) ≤
        219 / 5000) := by
  refine cell_assured_program_nominal_gain50_varying (mn := fun t => mn (⌈t * 10⌉₊ - 1))
    (m := fun t => m (⌈t * 10⌉₊ - 1)) (fc := fun t => fc (⌈t * 10⌉₊ - 1))
    (fv := fun t => fv (⌈t * 10⌉₊ - 1)) (acc := acc) (f := f) hsup hprog (fun _ => hmn _)
    (fun _ => hm _) hJ' (fun _ => hdm _) hdJ (fun _ => hfc _) (fun _ => hfv _) (fun _ => hcond _)
    hsamp (fun k t ht => ?_) hcont h0
  simp only [period_index ht]
  exact htrack k t ht

/-- **The assured cell at the gain 50 with the masses and the friction levels changing from period
to period, on exact samples.** As `cell_assured_program_nominal_gain50_switch`, with the samples
read in radians and rad/s equal to the true state at every boundary `k/10` s (`hexact`) in place of
`hsamp` (an exact sample is within every nonnegative error). A design statement, not from MLS
(computed torque of MLS eq. (4.49), p. 191; the plant's equations, MLS eq. (4.47), p. 190). -/
theorem cell_assured_program_nominal_gain50_switch_exact
    (hsup : Supervisor.Contract Instances.params)
    {reqs : ℕ → List Waypoint} {smp : ℕ → Policy.Sample} {st : ℕ → Policy.State}
    {acts : ℕ → List Action}
    (hprog : Policy.IsProgramRun Policy.designNominalGain50 reqs smp st acts)
    {J J' dm dJ : ℝ} {mn m fc fv : ℕ → ℝ} (hmn : ∀ k, 0 ≤ mn k) (hm : ∀ k, 0 ≤ m k)
    (hJ' : 3 / 2 ≤ J') (hdm : ∀ k, |m k - mn k| ≤ dm) (hdJ : |J' - J| ≤ dJ)
    (hfc : ∀ k, 0 ≤ fc k) (hfv : ∀ k, 0 ≤ fv k)
    (hcond : ∀ k, dm + 7 / 2 * dJ + (fc k + 4 * fv k) / 60 ≤ 3 / 2)
    {x v acc f : ℝ → Fin 3 → ℝ}
    (hexact : ∀ k : ℕ, x (k * (1 / 10)) = (smp k).toRad Policy.designNominalGain50 ∧
      v (k * (1 / 10)) = (smp k).velRad)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsNominalRightAt 50 2 J (mn k) J' (m k) (fc k) (fv k) x v acc f
        (DegPoint.toRad (st (k + 1)).src) (DegPoint.toRad (st (k + 1)).goal)
        ((st (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 50 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (st k).sup.faulted = false ∧ (st k).sup.age < 25) ∧
    (∀ k₀, (st k₀).sup.busy = false → (st (k₀ + 1)).sup.busy = true →
      (∀ j, j < 20 → (st (k₀ + 1 + j)).sup.busy = true) ∧
      (st (k₀ + 20 + 1)).sup.busy = false ∧ (st (k₀ + 20 + 1)).sup.current = (st (k₀ + 1)).goal) ∧
    (∀ k, (st k).sup.busy = true → (st (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (st k).goal)) ≤
        219 / 5000) :=
  cell_assured_program_nominal_gain50_switch hsup hprog hmn hm hJ' hdm hdJ hfc hfv hcond
    (fun k i => by rw [(hexact k).1, (hexact k).2, sub_self, sub_self, abs_zero]; norm_num)
    htrack hcont h0

/-- **The program at the gain 50 on encoder samples of a held run with a part picked up meets every
hypothesis of `cell_assured_program_nominal_gain50_switch`.** For a supervisor whose runs meet the
contract (`hsup`), the idle program at the configuration `Policy.designNominalGain50`, run on the
encoder samples (`2^18` counts per revolution, speeds floored to a multiple of `1/5` rad/s) of the
arm at rest at home, with the rotor inertia `17/10` kg m² on every joint in the controller's model
and in the plant, no part on the first period `(0, 1/10]` s (nominal and actual mass `0` kg, no
friction torque) and from then on the nominal mass `1` kg in the controller's model and the actual
mass `2` kg in the plant (a mass error of `1` kg) held by the friction torque
`(1 − 2) · toolGravity(home)` (at most `9` N m in every joint; `dm = 1` kg, `dJ = 0`, `f_c = 9` N m,
`f_v = 0` on every period, `1 + 9/60 ≤ 3/2`), meets every hypothesis of
`cell_assured_program_nominal_gain50_switch`; hence both links keep `9/100` m from every obstacle at
every `t ≥ 0` (s), the supervisor never faults and its age stays below 25, and the statements about
admissions and finishes hold (vacuously here, since nothing is admitted). A design statement, not
from MLS. -/
theorem program_hold_switch_nominal_gain50_assured (hsup : Supervisor.Contract Instances.params) :
    (∀ t : ℝ, 0 ≤ t → sceneClear (DegPoint.toRad Instances.params.home)) ∧
    (∀ k, (idleProgramNominalGain50 k).sup.faulted = false ∧
      (idleProgramNominalGain50 k).sup.age < 25) ∧
    (∀ k₀, (idleProgramNominalGain50 k₀).sup.busy = false →
      (idleProgramNominalGain50 (k₀ + 1)).sup.busy = true →
      (idleProgramNominalGain50 (k₀ + 20 + 1)).sup.busy = false ∧
        (idleProgramNominalGain50 (k₀ + 20 + 1)).sup.current =
          (idleProgramNominalGain50 (k₀ + 1)).goal) ∧
    (∀ k, (idleProgramNominalGain50 k).sup.busy = true →
      (idleProgramNominalGain50 (k + 1)).sup.busy = false →
      dist (sceneTool (DegPoint.toRad Instances.params.home))
        (sceneTool (DegPoint.toRad (idleProgramNominalGain50 k).goal)) ≤ 219 / 5000) := by
  set θ := DegPoint.toRad Instances.params.home with hθ
  have hg : ∀ i, |((1 - 2 : ℝ) • toolGravity θ) i| ≤ 9 := by
    have hR : |17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)| ≤ 817 / 1000 := by
      have := Real.neg_one_le_cos (θ 1)
      have := Real.cos_le_one (θ 1)
      have := Real.neg_one_le_cos (θ 1 + θ 2)
      have := Real.cos_le_one (θ 1 + θ 2)
      rw [abs_le]; constructor <;> linarith
    have hc := Real.abs_cos_le_one (θ 1 + θ 2)
    intro i
    fin_cases i <;> simp only [toolGravity, Pi.smul_apply, smul_eq_mul] <;> norm_num
    · linarith
    · linarith
  -- the friction torque: none on the first period, the held part's mass error from then on
  set fS : ℝ → Fin 3 → ℝ := fun t => (if t ≤ 1 / 10 then (0 : ℝ) else 1 - 2) • toolGravity θ
    with hfS
  -- at rest at home with the masses `mn'`, `m'` and the friction torque `(mn' − m') G(home)`
  have key : ∀ mn' m' : ℝ, 0 ≤ mn' → 0 ≤ m' → (∀ i, |((mn' - m') • toolGravity θ) i| ≤ 9) →
      ∀ (k : ℕ) (t : ℝ), fS t = (mn' - m') • toolGravity θ →
      CellArmFollowsNominalRightAt 50 2 (17 / 10) mn' (17 / 10) m' 9 0 (fun _ => θ) 0 0 fS
        (DegPoint.toRad (idleProgramNominalGain50 (k + 1)).src)
        (DegPoint.toRad (idleProgramNominalGain50 (k + 1)).goal)
        ((idleProgramNominalGain50 (k + 1)).start * (1 / 10)) t := by
    intro mn' m' hmn' hm' hb k t hft
    simp only [idleProgramNominalGain50, Policy.State.init, Policy.designNominalGain50]
    refine ⟨hasDerivWithinAt_const _ _ _, hasDerivWithinAt_const _ _ _, fun i => ?_, ?_⟩
    · rw [hft]
      simpa using hb i
    · simp only [Control.RobotSystem.computedTorque, Control.computedTorqueAlong]
      rw [moveRef_self, moveRefDeriv_self, moveRefDeriv2_self, ← hθ, hft]
      simp only [Pi.zero_apply, Matrix.mulVec_zero, zero_add, sub_self]
      rw [show (cellLoadedRobot (17 / 10) m').N θ 0 = cellArm.N θ 0 + m' • toolGravity θ from
          cellPayloadArm_N hm' θ 0,
        show (cellLoadedRobot (17 / 10) mn').N θ 0 = cellArm.N θ 0 + mn' • toolGravity θ from
          cellPayloadArm_N hmn' θ 0]
      module
  have htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsNominalRightAt 50 2 (17 / 10) (if k = 0 then 0 else 1) (17 / 10)
        (if k = 0 then 0 else 2) 9 0 (fun _ => θ) 0 0 fS
        (DegPoint.toRad (idleProgramNominalGain50 (k + 1)).src)
        (DegPoint.toRad (idleProgramNominalGain50 (k + 1)).goal)
        ((idleProgramNominalGain50 (k + 1)).start * (1 / 10)) t := by
    intro k t ht
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have ht' : t ≤ 1 / 10 := by simpa using ht.2
      simp only [↓reduceIte]
      exact key 0 0 le_rfl le_rfl (by simp) 0 t (by simp only [hfS, ht', ↓reduceIte, sub_self])
    · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have ht' : ¬t ≤ 1 / 10 := by
        have := ht.1
        intro h
        nlinarith
      simp only [hk.ne', ↓reduceIte]
      exact key 1 2 (by norm_num) (by norm_num) hg k t (by simp only [hfS, ht', ↓reduceIte])
  have hsamp : ∀ k : ℕ, ∀ i : Fin 3,
      |(encoderSample (fun _ => θ) 0 k).toRad Policy.designNominalGain50 i -
          (fun _ => θ) (k * (1 / 10)) i| ≤ 1 / 50 ∧
        |(encoderSample (fun _ => θ) 0 k).velRad i - (0 : ℝ → Fin 3 → ℝ) (k * (1 / 10)) i| ≤
          3 / 10 := by
    intro k i
    obtain ⟨h1, h2⟩ := encoderSample_within (fun _ => θ) 0 k i
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num)⟩
  have h0 : InTube (3 / 100) 50 (DegPoint.toRad Instances.params.home) 0
      ((fun _ => θ) 0) ((0 : ℝ → Fin 3 → ℝ) 0) := by
    intro i
    simp only [hθ, sub_self, Pi.zero_apply, mul_zero, add_zero, abs_zero]
    exact ⟨by norm_num, by norm_num⟩
  obtain ⟨h1, h2, h3, h4⟩ :=
    cell_assured_program_nominal_gain50_switch (J := 17 / 10) (J' := 17 / 10) (dm := 1) (dJ := 0)
    (mn := fun k => if k = 0 then 0 else 1) (m := fun k => if k = 0 then 0 else 2)
    (fc := fun _ => 9) (fv := fun _ => 0) hsup
    (idleProgramNominalGain50_isProgramRun (encoderSample (fun _ => θ) 0))
    (fun k => by split_ifs <;> norm_num) (fun k => by split_ifs <;> norm_num) (by norm_num)
    (fun k => by split_ifs <;> norm_num) (by norm_num) (fun _ => by norm_num) (fun _ => le_rfl)
    (fun _ => by norm_num) hsamp htrack
    (by simpa using (continuousOn_const :
      ContinuousOn (fun _ : ℝ => (θ, (0 : Fin 3 → ℝ))) (Ici 0))) h0
  exact ⟨h1, h2, fun k₀ hidle hbusy => (h3 k₀ hidle hbusy).2, h4⟩

end Cell.Loop
end RoboLean
