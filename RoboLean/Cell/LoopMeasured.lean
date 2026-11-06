import RoboLean.Cell.LoopOpen

/-!
# The assured sampled loop on measured samples

The loop of `RoboLean.Cell.LoopOpen` decides at each boundary `k h` from the exact sample
`(x (k h), v (k h))` of the motion. Here the decisions are taken from measured samples
`(xm k, vm k)` instead, each within `εq` (rad) of the true joint positions and within `εv`
(rad/s) of the true joint velocities in every joint (`SamplesWithin`).

* `SamplesWithin`, `IsMeasuredOpenRun`: the sample error bound and the timed runs of the open loop
  on measured samples.
* `MeasuredHyps`: the standing hypotheses of `OpenHyps` with the measured run, the sample error
  bound, and the tolerance conditions `δ + εq ≤ δ_a`, `2 ω δ + εv ≤ v_a`.
* `MeasuredHyps.assured`: the conclusions of `OpenHyps.assured` for every measured run whose states
  meet `LoopContract`.

The proof keeps the invariant `Inv` of `RoboLean.Cell.Assured`, which mentions no sample. A move is
never finished before it is due, whatever the sample; when it is due, the true state is in the tube
around the goal at rest, within `δ` and `2 ω δ`, so the measured sample is within `δ + εq` and
`2 ω δ + εv` and the arrival test on it passes. Hence the measured run is a run of the guarded loop
on the exact samples for the data with the arrival tolerances widened by `|εq|` and `|εv|`
(`Params.widen`), to which `Hyps.assured` applies; the widened data have the same waypoints,
links, period, duration and bound, so the conclusions carry over.

Every conclusion concerns the true motion `x`, `v`; none is about a quantity computed from the
samples. A design statement, not from MLS; it concerns the ideal sampled loop with a bounded sample
error and says nothing about a physical arm. Units as in `RoboLean.Cell.Loop`: seconds, radians,
radians per second; samples at the boundaries `k h`.
-/

namespace RoboLean.Cell.Loop

open Set

variable {n : ℕ} {W : Type*}

/-- The measured samples `xm k`, `vm k` at the boundaries `k h` are within `εq` (rad) of the true
joint positions `x (k h)` and within `εv` (rad/s) of the true joint velocities `v (k h)`, in every
joint. A design statement, not from MLS. -/
def SamplesWithin (P : Params n W) (εq εv : ℝ) (x v : ℝ → Fin n → ℝ) (xm vm : ℕ → Fin n → ℝ) :
    Prop :=
  ∀ k : ℕ, ∀ i : Fin n, |xm k i - x (k * P.period) i| ≤ εq ∧ |vm k i - v (k * P.period) i| ≤ εv

/-- A timed run of the open loop on measured samples: `s 0 = init home`, and `s (k + 1)` is an
`OpenStep` from `s k` with the measured sample `(xm k, vm k)` (rad, rad/s) taken at the boundary
`k h`. A design model, not from MLS. -/
def IsMeasuredOpenRun (P : Params n W) (home : W) (xm vm : ℕ → Fin n → ℝ) (s : ℕ → State W) :
    Prop :=
  s 0 = init home ∧ ∀ k : ℕ, OpenStep P k (xm k) (vm k) (s k) (s (k + 1))

/-- The standing hypotheses of the assured loop on measured samples: the fields of `OpenHyps`, with
the open run on the measured samples `(xm, vm)` in place of the exact ones, the sample error bound
`SamplesWithin` with `εq` (rad) and `εv` (rad/s), and arrival tolerances that leave room for the
sample error, `δ + εq ≤ δ_a` and `2 ω δ + εv ≤ v_a`. Seconds, radians, radians per second; samples
at the boundaries `k h`. A design statement, not from MLS. -/
structure MeasuredHyps (P : Params n W) (R : MoveRef n P.duration) (δ ω εq εv : ℝ) (home : W)
    (follows : W → W → ℝ → ℝ → Prop) (x v : ℝ → Fin n → ℝ) (xm vm : ℕ → Fin n → ℝ)
    (s : ℕ → State W) : Prop where
  /-- The period `h` (s) is positive. A design statement, not from MLS. -/
  period_pos : 0 < P.period
  /-- The move duration `T` (s) is positive. A design statement, not from MLS. -/
  duration_pos : 0 < P.duration
  /-- The age bound is at least the number of periods of a move, `⌈T / h⌉`. A design statement,
  not from MLS. -/
  ceil_le_bound : ⌈P.duration / P.period⌉₊ ≤ P.bound
  /-- The tube rate `ω` (1/s) is nonnegative. A design statement, not from MLS. -/
  rate_nonneg : 0 ≤ ω
  /-- The arrival position tolerance (rad) is at least the tube radius plus the position sample
  error. A design statement, not from MLS. -/
  radius_add_le_posTol : δ + εq ≤ P.posTol
  /-- The arrival speed tolerance (rad/s) is at least `2 ω δ` plus the velocity sample error. A
  design statement, not from MLS. -/
  speed_add_le_velTol : 2 * ω * δ + εv ≤ P.velTol
  /-- The home waypoint is linked to itself (it lies in a cell). A design statement, not from
  MLS. -/
  home_linked : P.linked home home
  /-- The decisions at the boundaries follow the open policy on the measured samples. A design
  statement, not from MLS. -/
  run : IsMeasuredOpenRun P home xm vm s
  /-- The measured samples are within `εq` (rad) and `εv` (rad/s) of the true state at the
  boundaries `k h`. A design statement, not from MLS. -/
  samples : SamplesWithin P εq εv x v xm vm
  /-- The controller tracks the reference of the last admitted move. A design statement, not from
  MLS. -/
  tracks : Tracks P follows s
  /-- The move corollary holds for the motion. A design statement, not from MLS. -/
  move : MoveCorollary P R δ ω follows x v
  /-- The arm starts in the tube around home at rest. A design statement, not from MLS. -/
  init_tube : InTube δ ω (P.pos home) 0 (x 0) (v 0)

/-- The loop data `P` with the arrival tolerances widened: the position tolerance by `a` (rad) and
the speed tolerance by `b` (rad/s); waypoints, links, period, duration and bound are unchanged. A
design definition, not from MLS. -/
noncomputable def Params.widen (P : Params n W) (a b : ℝ) : Params n W :=
  { P with posTol := P.posTol + a, velTol := P.velTol + b }

variable {P : Params n W} {R : MoveRef n P.duration} {δ ω εq εv : ℝ} {home : W}
  {follows : W → W → ℝ → ℝ → Prop} {x v : ℝ → Fin n → ℝ} {xm vm : ℕ → Fin n → ℝ}
  {s : ℕ → State W}

/-- `⌈T/h⌉` is positive for a positive duration and period (seconds). A design statement, not
from MLS. -/
theorem MeasuredHyps.steps_pos (H : MeasuredHyps P R δ ω εq εv home follows x v xm vm s) :
    0 < P.steps :=
  Nat.ceil_pos.mpr (div_pos H.duration_pos H.period_pos)

/-- `T ≤ ⌈T/h⌉ · h` (seconds). A design statement, not from MLS. -/
theorem MeasuredHyps.duration_le_steps_mul
    (H : MeasuredHyps P R δ ω εq εv home follows x v xm vm s) :
    P.duration ≤ P.steps * P.period := by
  have h1 := Nat.le_ceil (P.duration / P.period)
  have hp := H.period_pos
  calc P.duration = P.duration / P.period * P.period := by field_simp
    _ ≤ P.steps * P.period := mul_le_mul_of_nonneg_right h1 hp.le

/-- The time test of the policy in boundary counts: the move admitted at boundary `start` is due
at boundary `k` exactly when `start + ⌈T/h⌉ ≤ k`. A design statement, not from MLS. -/
theorem MeasuredHyps.due_iff (H : MeasuredHyps P R δ ω εq εv home follows x v xm vm s)
    (st : State W) (k : ℕ) : Due P st k ↔ st.start + P.steps ≤ k := by
  have hp := H.period_pos
  have hT := H.duration_pos
  constructor
  · intro hd
    unfold Due at hd
    have h0 : P.duration / P.period ≤ (k : ℝ) - st.start := by
      rw [div_le_iff₀ hp]; linarith
    have h1 : (st.start : ℝ) + P.duration / P.period ≤ k := by linarith
    have h2 : (st.start : ℝ) < k := by
      have := div_pos hT hp; linarith
    have h3 : st.start ≤ k := (Nat.cast_lt.mp h2).le
    have h4 : P.duration / P.period ≤ ((k - st.start : ℕ) : ℝ) := by
      rw [Nat.cast_sub h3]; linarith
    have := Nat.ceil_le.mpr h4
    unfold Params.steps; omega
  · intro hk
    unfold Due
    have h1 : ((st.start + P.steps : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at h1
    have h2 := H.duration_le_steps_mul
    nlinarith

/-- Under the invariant at boundary `k`, the motion is in the tube around the reference of the last
admitted move at every `t` (s) from its admission to `k h`. A design statement, not from MLS. -/
theorem MeasuredHyps.tube_of_inv (H : MeasuredHyps P R δ ω εq εv home follows x v xm vm s)
    {k : ℕ} {st : State W} (hI : Inv P δ ω follows x v k st) {t : ℝ}
    (ht : t ∈ Icc ((st.start : ℝ) * P.period) ((k : ℝ) * P.period)) :
    InTube δ ω (R.pos (P.pos st.src) (P.pos st.goal) (st.start * P.period) t)
      (R.vel (P.pos st.src) (P.pos st.goal) (st.start * P.period) t) (x t) (v t) := by
  have hp := H.period_pos
  have hs : ((st.start : ℕ) : ℝ) ≤ k := by exact_mod_cast hI.start_le
  exact H.move st.src st.goal hI.linked_move _ _ (by positivity)
    (mul_le_mul_of_nonneg_right hs hp.le) hI.follows_move hI.tube_start t ht

/-- If the true state at the boundary `k h` is in the tube around the goal `g` at rest, the
arrival test passes on the measured sample `(xm k, vm k)`: the sample is within `δ + εq` (rad) of
`g` and its speeds are at most `2 ω δ + εv` (rad/s). A design statement, not from MLS. -/
theorem MeasuredHyps.arrived_of_inTube (H : MeasuredHyps P R δ ω εq εv home follows x v xm vm s)
    {k : ℕ} {g : W} (h : InTube δ ω (P.pos g) 0 (x (k * P.period)) (v (k * P.period))) :
    Arrived P g (xm k) (vm k) := fun i => by
  obtain ⟨h1, h2⟩ := h.abs_le H.rate_nonneg i
  obtain ⟨hq, hv⟩ := H.samples k i
  have e1 := abs_sub_le (xm k i) (x (k * P.period) i) (P.pos g i)
  have e2 := abs_sub_abs_le_abs_sub (vm k i) (v (k * P.period) i)
  have t1 := H.radius_add_le_posTol
  have t2 := H.speed_add_le_velTol
  exact ⟨by linarith, by linarith⟩

/-- If the arrival test passes on the measured sample `(xm k, vm k)`, it passes on the true state
`(x (k h), v (k h))` for the tolerances widened by `|εq|` (rad) and `|εv|` (rad/s). A design
statement, not from MLS. -/
theorem MeasuredHyps.arrived_widen (H : MeasuredHyps P R δ ω εq εv home follows x v xm vm s)
    {k : ℕ} {g : W} (h : Arrived P g (xm k) (vm k)) :
    Arrived (P.widen |εq| |εv|) g (x (k * P.period)) (v (k * P.period)) := fun i => by
  obtain ⟨h1, h2⟩ := h i
  obtain ⟨hq, hv⟩ := H.samples k i
  rw [abs_sub_comm] at hq hv
  have e1 := abs_sub_le (x (k * P.period) i) (xm k i) (P.pos g i)
  have e2 := abs_sub_abs_le_abs_sub (v (k * P.period) i) (vm k i)
  have a1 := le_abs_self εq
  have a2 := le_abs_self εv
  show |x (k * P.period) i - P.pos g i| ≤ P.posTol + |εq| ∧
    |v (k * P.period) i| ≤ P.velTol + |εv|
  exact ⟨by linarith, by linarith⟩

/-- The invariant holds at the initial state. A design statement, not from MLS. -/
theorem MeasuredHyps.inv_zero (H : MeasuredHyps P R δ ω εq εv home follows x v xm vm s) :
    Inv P δ ω follows x v 0 (init home) where
  faulted_eq := rfl
  linked_move := H.home_linked
  start_le := le_rfl
  follows_move := by
    intro t ht
    simp only [init, Nat.cast_zero, zero_mul, Set.mem_Ioc] at ht
    exact absurd ht.2 (not_le.mpr ht.1)
  tube_start := by simpa [init] using H.init_tube
  busy_spec := by intro h; simp [init] at h
  idle_spec := fun _ => ⟨rfl, rfl, Or.inl rfl⟩

/-- One boundary preserves the invariant on measured samples: from the invariant at boundary `k`,
a decision of the guarded policy with the measured sample `(xm k, vm k)`, and tracking of the new
state's last move on `(k h, (k + 1) h]`, the invariant holds at boundary `k + 1`. A tick cannot
happen when the move is due, since the arrival test then passes on the sample. A design statement,
not from MLS. -/
theorem MeasuredHyps.inv_step (H : MeasuredHyps P R δ ω εq εv home follows x v xm vm s) {k : ℕ}
    {st st' : State W} (hI : Inv P δ ω follows x v k st)
    (hstep : Step P k (xm k) (vm k) st st')
    (htr : ∀ t ∈ Ioc ((k : ℝ) * P.period) ((k + 1) * P.period),
      follows st'.src st'.goal (st'.start * P.period) t) :
    Inv P δ ω follows x v (k + 1) st' := by
  have hp := H.period_pos
  have hk : ((st.start : ℕ) : ℝ) * P.period ≤ (k : ℝ) * P.period :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hI.start_le) hp.le
  have htube := H.tube_of_inv hI ⟨hk, le_rfl⟩
  -- the motion followed the move of `st` up to `(k + 1) h` when the move is unchanged
  have hext : ∀ st'' : State W, st''.src = st.src → st''.goal = st.goal → st''.start = st.start →
      (∀ t ∈ Ioc ((k : ℝ) * P.period) ((k + 1) * P.period),
        follows st''.src st''.goal (st''.start * P.period) t) →
      ∀ t ∈ Ioc ((st''.start : ℝ) * P.period) (((k + 1 : ℕ) : ℝ) * P.period),
        follows st''.src st''.goal (st''.start * P.period) t := by
    intro st'' h1 h2 h3 hnew t ht
    rw [h1, h2, h3] at hnew ⊢
    rw [h3] at ht
    push_cast at ht
    by_cases htk : t ≤ (k : ℝ) * P.period
    · exact hI.follows_move t ⟨ht.1, htk⟩
    · exact hnew t ⟨not_le.mp htk, ht.2⟩
  cases hstep with
  | finish hbusy hdue harr =>
    obtain ⟨-, hage, -⟩ := hI.busy_spec hbusy
    have hd := (H.due_iff st k).mp hdue
    exact {
      faulted_eq := hI.faulted_eq
      linked_move := hI.linked_move
      start_le := hI.start_le.trans (Nat.le_succ k)
      follows_move := hext _ rfl rfl rfl htr
      tube_start := hI.tube_start
      busy_spec := by intro h; simp at h
      idle_spec := fun _ => ⟨rfl, rfl, Or.inr (by dsimp only; omega)⟩ }
  | timeout hbusy hnot hage =>
    obtain ⟨-, -, hlt⟩ := hI.busy_spec hbusy
    have := H.ceil_le_bound
    unfold Params.steps at hlt
    omega
  | tick hbusy hnot hage =>
    obtain ⟨hcur, hsum, hlt⟩ := hI.busy_spec hbusy
    have hlt' : st.age + 1 < P.steps := by
      by_contra hge
      apply hnot
      have hdue : Due P st k := (H.due_iff st k).mpr (by omega)
      refine ⟨hdue, H.arrived_of_inTube ?_⟩
      have hrest := R.rest (a := P.pos st.src) (b := P.pos st.goal)
        (t₀ := st.start * P.period) (t := k * P.period) (Or.inr hdue)
      rw [hrest.1, hrest.2] at htube
      exact htube
    exact {
      faulted_eq := hI.faulted_eq
      linked_move := hI.linked_move
      start_le := hI.start_le.trans (Nat.le_succ k)
      follows_move := hext _ rfl rfl rfl htr
      tube_start := hI.tube_start
      busy_spec := fun _ => ⟨hcur, by simp only; omega, hlt'⟩
      idle_spec := by intro h; simp [hbusy] at h }
  | wait hidle =>
    obtain ⟨hcur, hage, hrest⟩ := hI.idle_spec hidle
    exact {
      faulted_eq := hI.faulted_eq
      linked_move := hI.linked_move
      start_le := hI.start_le.trans (Nat.le_succ k)
      follows_move := hext _ rfl rfl rfl htr
      tube_start := hI.tube_start
      busy_spec := by intro h; simp [hidle] at h
      idle_spec := fun _ => ⟨hcur, hage, hrest.imp_right (fun h => by omega)⟩ }
  | admit w hidle hok hlinked =>
    obtain ⟨hcur, -, hrest⟩ := hI.idle_spec hidle
    have hset : (st.src = st.goal) ∨ st.start * P.period + P.duration ≤ (k : ℝ) * P.period := by
      rcases hrest with h | h
      · exact Or.inl h
      · exact Or.inr ((H.due_iff st k).mpr h.le)
    have hrest' := R.rest (a := P.pos st.src) (b := P.pos st.goal)
      (t₀ := st.start * P.period) (t := k * P.period)
      (hset.imp_left (fun h => by rw [h]))
    rw [hrest'.1, hrest'.2] at htube
    have hpos := H.steps_pos
    exact {
      faulted_eq := hok
      linked_move := hlinked
      start_le := Nat.le_succ k
      follows_move := by
        intro t ht
        apply htr t
        simpa using ht
      tube_start := by simpa [hcur] using htube
      busy_spec := fun _ => ⟨rfl, by simp, hpos⟩
      idle_spec := by intro h; simp at h }

/-- Along a measured run whose states meet the contract, each decision is a step of the guarded
loop on the measured sample `(xm k, vm k)`. A design statement, not from MLS. -/
theorem MeasuredHyps.step (H : MeasuredHyps P R δ ω εq εv home follows x v xm vm s)
    (hc : LoopContract P s) (k : ℕ) : Step P k (xm k) (vm k) (s k) (s (k + 1)) :=
  (H.run.2 k).step (hc (k + 1)).1 (hc (k + 1)).2

/-- **The loop invariant on measured samples.** Along every measured run under `MeasuredHyps`
whose states meet the contract, the invariant `Inv` holds at every boundary. A design statement,
not from MLS. -/
theorem MeasuredHyps.inv (H : MeasuredHyps P R δ ω εq εv home follows x v xm vm s)
    (hc : LoopContract P s) (k : ℕ) : Inv P δ ω follows x v k (s k) := by
  induction k with
  | zero => rw [H.run.1]; exact H.inv_zero
  | succ k ih => exact H.inv_step ih (H.step hc k) (H.tracks k)

/-- Under the invariant at boundary `k`, a step of the guarded loop on the measured sample
`(xm k, vm k)` is a step of the guarded loop on the exact sample `(x (k h), v (k h))` for the
tolerances widened by `|εq|` (rad) and `|εv|` (rad/s): a finish arrived on the sample arrives on
the true state within the widened tolerances, a timeout cannot happen, and a tick happens only
when the move is not due. A design statement, not from MLS. -/
theorem MeasuredHyps.step_widen (H : MeasuredHyps P R δ ω εq εv home follows x v xm vm s)
    {k : ℕ} {st st' : State W} (hI : Inv P δ ω follows x v k st)
    (hstep : Step P k (xm k) (vm k) st st') :
    Step (P.widen |εq| |εv|) k (x (k * P.period)) (v (k * P.period)) st st' := by
  cases hstep with
  | finish hbusy hdue harr => exact .finish _ hbusy hdue (H.arrived_widen harr)
  | timeout hbusy hnot hage =>
    obtain ⟨-, -, hlt⟩ := hI.busy_spec hbusy
    have := H.ceil_le_bound
    unfold Params.steps at hlt
    omega
  | tick hbusy hnot hage =>
    refine .tick _ hbusy (fun hfin => hnot ⟨hfin.1, H.arrived_of_inTube ?_⟩) hage
    have hp := H.period_pos
    have hk : ((st.start : ℕ) : ℝ) * P.period ≤ (k : ℝ) * P.period :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hI.start_le) hp.le
    have htube := H.tube_of_inv hI ⟨hk, le_rfl⟩
    have hrest := R.rest (a := P.pos st.src) (b := P.pos st.goal)
      (t₀ := st.start * P.period) (t := k * P.period) (Or.inr hfin.1)
    rw [hrest.1, hrest.2] at htube
    exact htube
  | wait hidle => exact .wait _ hidle
  | admit w hidle hok hlinked => exact .admit _ w hidle hok hlinked

/-- **A measured run is a run of the guarded loop on the exact samples, for widened tolerances.**
Along a measured run under `MeasuredHyps` whose states meet the contract, the standing hypotheses
`Hyps` hold for the data with the arrival tolerances widened by `|εq|` (rad) and `|εv|` (rad/s)
and the exact samples `(x (k h), v (k h))`. A design statement, not from MLS. -/
theorem MeasuredHyps.hyps (H : MeasuredHyps P R δ ω εq εv home follows x v xm vm s)
    (hc : LoopContract P s) : Hyps (P.widen |εq| |εv|) R δ ω home follows x v s where
  period_pos := H.period_pos
  duration_pos := H.duration_pos
  ceil_le_bound := H.ceil_le_bound
  rate_nonneg := H.rate_nonneg
  radius_le_posTol := by
    have := H.radius_add_le_posTol
    have := neg_abs_le εq
    show δ ≤ P.posTol + |εq|
    linarith
  speed_le_velTol := by
    have := H.speed_add_le_velTol
    have := neg_abs_le εv
    show 2 * ω * δ ≤ P.velTol + |εv|
    linarith
  home_linked := H.home_linked
  run := ⟨H.run.1, fun k => H.step_widen (H.inv hc k) (H.step hc k)⟩
  tracks := H.tracks
  move := H.move
  init_tube := H.init_tube

/-- **The assured loop on measured samples.** Along every timed run of the open loop whose
decisions are taken from measured samples within `εq` (rad) and `εv` (rad/s) of the true state at
the boundaries, under `MeasuredHyps` (in particular `δ + εq ≤ δ_a` and `2 ω δ + εv ≤ v_a`), whose
states meet the loop-level contract `LoopContract`, with cells certified at an inflation
`δ_c ≥ δ` and a tool map with the Lipschitz-type bound `L`:
(a) the configuration is clear at every instant `t ≥ 0`;
(b) the supervisor is never faulted, the age stays below the bound, and a move admitted at
boundary `k₀` is finished at boundary `k₀ + ⌈T/h⌉` with the arm at its goal;
(c) at each finish the tool at the true configuration is within `L δ` of the goal's tool position;
(d) at each finish the true motion is in the tube around the goal at rest.
The conclusions are those of `OpenHyps.assured`. Seconds, radians, radians per second; samples at
the boundaries `k h`. A design statement, not from MLS. -/
theorem MeasuredHyps.assured {E : Type*} [PseudoMetricSpace E]
    (H : MeasuredHyps P R δ ω εq εv home follows x v xm vm s) (hc : LoopContract P s)
    {δc : ℝ} {clear : (Fin n → ℝ) → Prop} (hcert : CellsCertify P δc clear) (hδ : δ ≤ δc)
    {tool : (Fin n → ℝ) → E} {L : ℝ}
    (htool : ∀ θ θ' : Fin n → ℝ, ∀ r : ℝ, (∀ i, |θ i - θ' i| ≤ r) →
      dist (tool θ) (tool θ') ≤ L * r) :
    (∀ t, 0 ≤ t → clear (x t)) ∧
    (∀ k, (s k).faulted = false ∧ (s k).age < P.bound) ∧
    (∀ k₀, (s k₀).busy = false → (s (k₀ + 1)).busy = true →
      (∀ j, j < P.steps → (s (k₀ + 1 + j)).busy = true) ∧
      (s (k₀ + P.steps + 1)).busy = false ∧
      (s (k₀ + P.steps + 1)).current = (s (k₀ + 1)).goal) ∧
    (∀ k, (s k).busy = true → (s (k + 1)).busy = false →
      dist (tool (x (k * P.period))) (tool (P.pos (s k).goal)) ≤ L * δ) ∧
    (∀ k, (s k).busy = true → (s (k + 1)).busy = false →
      (s (k + 1)).current = (s k).goal ∧
      InTube δ ω (P.pos (s k).goal) 0 (x (k * P.period)) (v (k * P.period))) :=
  (H.hyps hc).assured hcert hδ htool

end RoboLean.Cell.Loop
