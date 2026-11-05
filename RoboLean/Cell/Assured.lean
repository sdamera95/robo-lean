import RoboLean.Cell.Loop

/-!
# The assured sampled loop: clearance, finish on time, tool accuracy and handoff

For the sampled loop of `RoboLean.Cell.Loop` under the standing hypotheses `Hyps` (the policy at
the boundaries, tracking of the last admitted move between them, the move corollary for the
motion, the tube around home at time `0`, and numeric conditions on the period, the duration, the
age bound and the arrival tolerances), this file proves, along every timed run:

* `Hyps.tube`: at every instant of every period the motion is in the tube around the reference of
  the move in force;
* `Hyps.mem_inflate`, `Hyps.clear`: the configuration lies in the inflation by `δ` of every convex
  cell containing the two waypoints of the move in force, hence is clear when the cells are
  certified at an inflation `δ_c ≥ δ` (`CellsCertify`);
* `Hyps.finish_on_time`: a move admitted at boundary `k₀` is busy at the boundaries
  `k₀ + 1, …, k₀ + ⌈T/h⌉ − 1` and finished at boundary `k₀ + ⌈T/h⌉`, at its goal;
  `Hyps.age_lt_bound` and `Hyps.faulted_eq_false`: the age never reaches the bound, so no timeout
  occurs and the supervisor never faults;
* `Hyps.tube_of_finish`, `Hyps.tool_dist_of_finish`: at each finish the arm is in the tube around
  the goal at rest, and the tool is within `L δ` of the goal's tool position for a tool map with
  `dist (tool θ) (tool θ') ≤ L r` whenever `|θᵢ − θ'ᵢ| ≤ r` for all `i`;
* `Hyps.tube_of_idle`: while idle the arm stays in the tube around the waypoint it is at, which is
  the tube at the start of the next admitted move (the handoff).

`Hyps.assured` collects the conclusions. The proof is an induction over the boundaries with the
invariant `Inv`. A design statement, not from MLS; it concerns the ideal sampled loop with exact
samples and says nothing about a physical arm.
-/

namespace RoboLean.Cell.Loop

open Set

variable {n : ℕ} {W : Type*}

/-- The number of periods of a move, `⌈T / h⌉`. A design statement, not from MLS. -/
noncomputable def Params.steps (P : Params n W) : ℕ :=
  ⌈P.duration / P.period⌉₊

/-- The invariant of the loop state `st` before the decision at boundary `k`: not faulted; the
last admitted move is linked and was admitted at a boundary `start ≤ k`; the motion followed its
reference on `(start · h, k h]` and was in the tube around its start at rest at `start · h`; while
busy, the arm's waypoint is the move's start, `start + age + 1 = k` and `age < ⌈T/h⌉`; while idle,
the arm's waypoint is the move's goal, the age is zero, and the move is a rest move or ended more
than a full period before `k h` (`start + ⌈T/h⌉ < k`). A design statement, not from MLS. -/
structure Inv (P : Params n W) (δ ω : ℝ) (follows : W → W → ℝ → ℝ → Prop)
    (x v : ℝ → Fin n → ℝ) (k : ℕ) (st : State W) : Prop where
  /-- Not faulted. -/
  faulted_eq : st.faulted = false
  /-- The last admitted move is linked. -/
  linked_move : P.linked st.src st.goal
  /-- The last admitted move was admitted at a boundary `start ≤ k`. -/
  start_le : st.start ≤ k
  /-- The motion followed the reference of the last admitted move since its admission. -/
  follows_move : ∀ t ∈ Ioc ((st.start : ℝ) * P.period) ((k : ℝ) * P.period),
    follows st.src st.goal (st.start * P.period) t
  /-- The motion was in the tube around the move's start at its admission. -/
  tube_start : InTube δ ω (P.pos st.src) 0 (x (st.start * P.period)) (v (st.start * P.period))
  /-- The busy facts. -/
  busy_spec : st.busy = true →
    st.current = st.src ∧ st.start + st.age + 1 = k ∧ st.age < P.steps
  /-- The idle facts. -/
  idle_spec : st.busy = false →
    st.current = st.goal ∧ st.age = 0 ∧ (st.src = st.goal ∨ st.start + P.steps < k)

variable {P : Params n W} {R : MoveRef n P.duration} {δ ω : ℝ} {home : W}
  {follows : W → W → ℝ → ℝ → Prop} {x v : ℝ → Fin n → ℝ} {s : ℕ → State W}

/-- `⌈T/h⌉` is positive for a positive duration and period. A design statement, not from MLS. -/
theorem Hyps.steps_pos (H : Hyps P R δ ω home follows x v s) : 0 < P.steps :=
  Nat.ceil_pos.mpr (div_pos H.duration_pos H.period_pos)

/-- `T ≤ ⌈T/h⌉ · h`. A design statement, not from MLS. -/
theorem Hyps.duration_le_steps_mul (H : Hyps P R δ ω home follows x v s) :
    P.duration ≤ P.steps * P.period := by
  have h1 := Nat.le_ceil (P.duration / P.period)
  have hp := H.period_pos
  calc P.duration = P.duration / P.period * P.period := by field_simp
    _ ≤ P.steps * P.period := mul_le_mul_of_nonneg_right h1 hp.le

/-- The time test of the policy in boundary counts: the move admitted at boundary `start` is due
at boundary `k` exactly when `start + ⌈T/h⌉ ≤ k`. A design statement, not from MLS. -/
theorem Hyps.due_iff (H : Hyps P R δ ω home follows x v s) (st : State W) (k : ℕ) :
    Due P st k ↔ st.start + P.steps ≤ k := by
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

/-- A rest move, or any move from `t₀ + T` on, has its reference at the goal with zero velocity. A
design statement, not from MLS. -/
theorem MoveRef.rest {T : ℝ} (R : MoveRef n T) {a b : Fin n → ℝ} {t₀ t : ℝ}
    (h : a = b ∨ t₀ + T ≤ t) : R.pos a b t₀ t = b ∧ R.vel a b t₀ t = 0 := by
  rcases h with rfl | h
  · have hmem := R.pos_mem_segment a a t₀ t
    rw [segment_same] at hmem
    exact ⟨hmem, R.vel_self a t₀ t⟩
  · exact ⟨R.pos_of_le a b t₀ t h, R.vel_of_le a b t₀ t h⟩

/-- In the tube around `p` at rest, the joints are within `δ` of `p` and their speeds are at most
`2 ω δ`, for `ω ≥ 0`. A design statement, not from MLS. -/
theorem InTube.abs_le {p θ θ' : Fin n → ℝ} (h : InTube δ ω p 0 θ θ') (hω : 0 ≤ ω) (i : Fin n) :
    |θ i - p i| ≤ δ ∧ |θ' i| ≤ 2 * ω * δ := by
  obtain ⟨he, hz⟩ := h i
  refine ⟨he, ?_⟩
  simp only [Pi.zero_apply, sub_zero] at hz
  have h1 : |ω * (θ i - p i)| ≤ ω * δ := by
    rw [abs_mul, abs_of_nonneg hω]; exact mul_le_mul_of_nonneg_left he hω
  have h2 : θ' i = (θ' i + ω * (θ i - p i)) - ω * (θ i - p i) := by ring
  calc |θ' i| = |(θ' i + ω * (θ i - p i)) - ω * (θ i - p i)| := by rw [← h2]
    _ ≤ |θ' i + ω * (θ i - p i)| + |ω * (θ i - p i)| := abs_sub _ _
    _ ≤ ω * δ + ω * δ := add_le_add hz h1
    _ = 2 * ω * δ := by ring

/-- In the tube around the goal at rest the arrival test passes. A design statement, not from
MLS. -/
theorem Hyps.arrived_of_inTube (H : Hyps P R δ ω home follows x v s) {g : W} {θ θ' : Fin n → ℝ}
    (h : InTube δ ω (P.pos g) 0 θ θ') : Arrived P g θ θ' := fun i => by
  obtain ⟨h1, h2⟩ := h.abs_le H.rate_nonneg i
  exact ⟨h1.trans H.radius_le_posTol, h2.trans H.speed_le_velTol⟩

/-- Under the invariant at boundary `k`, the motion is in the tube around the reference of the last
admitted move at every `t` from its admission to `k h`. A design statement, not from MLS. -/
theorem Hyps.tube_of_inv (H : Hyps P R δ ω home follows x v s) {k : ℕ} {st : State W}
    (hI : Inv P δ ω follows x v k st) {t : ℝ}
    (ht : t ∈ Icc ((st.start : ℝ) * P.period) ((k : ℝ) * P.period)) :
    InTube δ ω (R.pos (P.pos st.src) (P.pos st.goal) (st.start * P.period) t)
      (R.vel (P.pos st.src) (P.pos st.goal) (st.start * P.period) t) (x t) (v t) := by
  have hp := H.period_pos
  have hs : ((st.start : ℕ) : ℝ) ≤ k := by exact_mod_cast hI.start_le
  exact H.move st.src st.goal hI.linked_move _ _ (by positivity)
    (mul_le_mul_of_nonneg_right hs hp.le) hI.follows_move hI.tube_start t ht

/-- The invariant holds at the initial state. A design statement, not from MLS. -/
theorem Hyps.inv_zero (H : Hyps P R δ ω home follows x v s) :
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

/-- One boundary preserves the invariant: from the invariant at boundary `k`, a decision of the
policy with the sample at `k h`, and tracking of the new state's last move on `(k h, (k + 1) h]`,
the invariant holds at boundary `k + 1`. A design statement, not from MLS. -/
theorem Hyps.inv_step (H : Hyps P R δ ω home follows x v s) {k : ℕ} {st st' : State W}
    (hI : Inv P δ ω follows x v k st)
    (hstep : Step P k (x (k * P.period)) (v (k * P.period)) st st')
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

/-- **The loop invariant.** Along every timed run under the standing hypotheses, the invariant
`Inv` holds at every boundary. By induction over the boundaries from `Hyps.inv_zero` and
`Hyps.inv_step`. A design statement, not from MLS. -/
theorem Hyps.inv (H : Hyps P R δ ω home follows x v s) (k : ℕ) :
    Inv P δ ω follows x v k (s k) := by
  induction k with
  | zero => rw [H.run.1]; exact H.inv_zero
  | succ k ih => exact H.inv_step ih (H.run.2 k) (H.tracks k)

/-- The last admitted move in force on the period after boundary `k` was admitted at a boundary
`start ≤ k`. A design statement, not from MLS. -/
theorem Hyps.start_succ_le (H : Hyps P R δ ω home follows x v s) (k : ℕ) :
    (s (k + 1)).start ≤ k := by
  have hI := H.inv k
  have hstep := H.run.2 k
  generalize s (k + 1) = st' at hstep
  cases hstep with
  | admit => exact le_rfl
  | finish => exact hI.start_le
  | timeout => exact hI.start_le
  | tick => exact hI.start_le
  | wait => exact hI.start_le

/-- **Tracking along the run.** At every instant `t` of the period from `k h` to `(k + 1) h`, the
motion is in the tube of radius `δ` and rate `ω` around the reference of the move in force, the
last admitted move of `s (k + 1)`. A design statement, not from MLS. -/
theorem Hyps.tube (H : Hyps P R δ ω home follows x v s) (k : ℕ) {t : ℝ}
    (ht : t ∈ Icc ((k : ℝ) * P.period) ((k + 1) * P.period)) :
    InTube δ ω (R.pos (P.pos (s (k + 1)).src) (P.pos (s (k + 1)).goal)
        ((s (k + 1)).start * P.period) t)
      (R.vel (P.pos (s (k + 1)).src) (P.pos (s (k + 1)).goal) ((s (k + 1)).start * P.period) t)
      (x t) (v t) := by
  have hp := H.period_pos
  have hs : (((s (k + 1)).start : ℕ) : ℝ) ≤ k := by exact_mod_cast H.start_succ_le k
  refine H.tube_of_inv (H.inv (k + 1)) ⟨(mul_le_mul_of_nonneg_right hs hp.le).trans ht.1, ?_⟩
  push_cast; exact ht.2

/-- **In the inflated cell (conclusion (a)).** At every instant `t` of the period from `k h` to
`(k + 1) h`, the joint vector `x t` lies in the inflation by `δ` of every convex set `C` that
contains the joint vectors of the two waypoints of the move in force: the reference lies on the
segment between them, hence in `C`, and the motion is within `δ` of it in every joint. A design
statement, not from MLS. -/
theorem Hyps.mem_inflate (H : Hyps P R δ ω home follows x v s) (k : ℕ) {t : ℝ}
    (ht : t ∈ Icc ((k : ℝ) * P.period) ((k + 1) * P.period)) {C : Set (Fin n → ℝ)}
    (hC : Convex ℝ C) (ha : P.pos (s (k + 1)).src ∈ C) (hb : P.pos (s (k + 1)).goal ∈ C) :
    x t ∈ inflate δ C :=
  ⟨_, hC.segment_subset ha hb (R.pos_mem_segment _ _ _ _), fun i => (H.tube k ht i).1⟩

/-- Inflation is monotone in the radius. A design statement, not from MLS. -/
theorem inflate_mono {r r' : ℝ} (h : r ≤ r') (C : Set (Fin n → ℝ)) :
    inflate r C ⊆ inflate r' C := fun _ ⟨c, hc, hci⟩ => ⟨c, hc, fun i => (hci i).trans h⟩

/-- **Clearance (conclusion (a)).** If the cells are certified at an inflation `δ_c ≥ δ`
(`CellsCertify`), then the configuration `x t` is clear at every instant `t ≥ 0`. A design
statement, not from MLS. -/
theorem Hyps.clear (H : Hyps P R δ ω home follows x v s) {δc : ℝ}
    {clear : (Fin n → ℝ) → Prop} (hcert : CellsCertify P δc clear) (hδ : δ ≤ δc) {t : ℝ}
    (ht : 0 ≤ t) : clear (x t) := by
  have hp := H.period_pos
  set k := ⌊t / P.period⌋₊
  have hk : t ∈ Icc ((k : ℝ) * P.period) ((k + 1) * P.period) := by
    have h1 := Nat.floor_le (div_nonneg ht hp.le)
    have h2 := Nat.lt_floor_add_one (t / P.period)
    constructor
    · rwa [le_div_iff₀ hp] at h1
    · exact (le_of_lt ((div_lt_iff₀ hp).mp h2))
  obtain ⟨C, hC, ha, hb, hclear⟩ := hcert _ _ (H.inv (k + 1)).linked_move
  exact hclear _ (inflate_mono hδ C (H.mem_inflate k hk hC ha hb))

/-- **Never faulted (conclusion (b)).** Along every timed run under the standing hypotheses the
supervisor is never faulted, so no timeout occurs. A design statement, not from MLS. -/
theorem Hyps.faulted_eq_false (H : Hyps P R δ ω home follows x v s) (k : ℕ) :
    (s k).faulted = false :=
  (H.inv k).faulted_eq

/-- **The age never reaches the bound (conclusion (b)).** Along every timed run under the standing
hypotheses, `age < bound` at every boundary (`age < ⌈T/h⌉ ≤ bound` while busy, `0` while idle).
A design statement, not from MLS. -/
theorem Hyps.age_lt_bound (H : Hyps P R δ ω home follows x v s) (k : ℕ) :
    (s k).age < P.bound := by
  have hI := H.inv k
  have h1 := H.ceil_le_bound
  have h2 := H.steps_pos
  unfold Params.steps at h2
  cases hb : (s k).busy
  · rw [(hI.idle_spec hb).2.1]; omega
  · have := (hI.busy_spec hb).2.2; unfold Params.steps at this; omega

/-- **Every finish is at the goal in the tube (conclusion (d)).** If the loop is busy at boundary
`k` and idle after it, the decision was a finish: the arm's waypoint is now the goal of the move,
and at `k h` the motion is in the tube around the goal at rest, which is the tube at the start of
the next move. A design statement, not from MLS. -/
theorem Hyps.tube_of_finish (H : Hyps P R δ ω home follows x v s) {k : ℕ}
    (hbusy : (s k).busy = true) (hidle : (s (k + 1)).busy = false) :
    (s (k + 1)).current = (s k).goal ∧
      InTube δ ω (P.pos (s k).goal) 0 (x (k * P.period)) (v (k * P.period)) := by
  have hI := H.inv k
  have hfault := H.faulted_eq_false (k + 1)
  have hp := H.period_pos
  have hstep := H.run.2 k
  generalize s (k + 1) = st' at hstep hidle hfault ⊢
  have hk : (((s k).start : ℕ) : ℝ) * P.period ≤ (k : ℝ) * P.period :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hI.start_le) hp.le
  have htube := H.tube_of_inv hI ⟨hk, le_rfl⟩
  cases hstep with
  | finish _ hdue _ =>
    refine ⟨rfl, ?_⟩
    have hrest := R.rest (a := P.pos (s k).src) (b := P.pos (s k).goal)
      (t₀ := (s k).start * P.period) (t := k * P.period) (Or.inr hdue)
    rw [hrest.1, hrest.2] at htube
    exact htube
  | timeout => simp at hfault
  | tick => simp [hbusy] at hidle
  | wait h => simp [hbusy] at h
  | admit => simp at hidle

/-- **Tool accuracy at each finish (conclusion (c)).** For a tool map `tool` into a pseudometric
space with `dist (tool θ) (tool θ') ≤ L r` whenever `|θᵢ − θ'ᵢ| ≤ r` for every joint, at each
finish (busy at boundary `k`, idle after it) the tool at `x (k h)` is within `L δ` of the goal's
tool position. A design statement, not from MLS. -/
theorem Hyps.tool_dist_of_finish {E : Type*} [PseudoMetricSpace E]
    (H : Hyps P R δ ω home follows x v s) {tool : (Fin n → ℝ) → E} {L : ℝ}
    (htool : ∀ θ θ' : Fin n → ℝ, ∀ r : ℝ, (∀ i, |θ i - θ' i| ≤ r) →
      dist (tool θ) (tool θ') ≤ L * r)
    {k : ℕ} (hbusy : (s k).busy = true) (hidle : (s (k + 1)).busy = false) :
    dist (tool (x (k * P.period))) (tool (P.pos (s k).goal)) ≤ L * δ :=
  htool _ _ δ fun i => ((H.tube_of_finish hbusy hidle).2 i).1

/-- **Resting in the tube while idle (conclusion (d), the handoff).** If the loop is idle on the
period from `k h` to `(k + 1) h`, the motion stays in the tube around the waypoint the arm is at,
at rest, throughout the period; in particular at the next admission it is in the tube around the
start of the admitted move. A design statement, not from MLS. -/
theorem Hyps.tube_of_idle (H : Hyps P R δ ω home follows x v s) (k : ℕ)
    (hidle : (s (k + 1)).busy = false) {t : ℝ}
    (ht : t ∈ Icc ((k : ℝ) * P.period) ((k + 1) * P.period)) :
    InTube δ ω (P.pos (s (k + 1)).current) 0 (x t) (v t) := by
  have hI := H.inv (k + 1)
  obtain ⟨hcur, -, hrest⟩ := hI.idle_spec hidle
  have htube := H.tube k ht
  have hp := H.period_pos
  have hset : (s (k + 1)).src = (s (k + 1)).goal ∨
      ((s (k + 1)).start : ℝ) * P.period + P.duration ≤ t := by
    rcases hrest with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans ?_ ht.1)
      have hd : Due P (s (k + 1)) k := (H.due_iff (s (k + 1)) k).mpr (by omega)
      exact hd
  have hrest' := R.rest (a := P.pos (s (k + 1)).src) (b := P.pos (s (k + 1)).goal)
    (t₀ := (s (k + 1)).start * P.period) (t := t) (hset.imp_left (fun h => by rw [h]))
  rw [hrest'.1, hrest'.2] at htube
  rw [hcur]; exact htube

/-- An admission at boundary `k₀` (idle at `k₀`, busy after it) starts the move from the arm's
waypoint at boundary `k₀` with start boundary `k₀` and age `0`. A design statement, not from MLS. -/
theorem Hyps.admit_spec (H : Hyps P R δ ω home follows x v s) {k₀ : ℕ}
    (hidle : (s k₀).busy = false) (hbusy : (s (k₀ + 1)).busy = true) :
    (s (k₀ + 1)).src = (s k₀).current ∧ (s (k₀ + 1)).current = (s k₀).current ∧
      (s (k₀ + 1)).start = k₀ ∧ (s (k₀ + 1)).age = 0 := by
  have hstep := H.run.2 k₀
  generalize s (k₀ + 1) = st' at hstep hbusy ⊢
  cases hstep with
  | admit => exact ⟨rfl, rfl, rfl, rfl⟩
  | finish h => simp [hidle] at h
  | timeout h => simp [hidle] at h
  | tick h => simp [hidle] at h
  | wait => simp [hidle] at hbusy

/-- One boundary of a busy loop with a move admitted at `k₀` that is not yet due: the decision is a
tick, which keeps the move and increments the age. A design statement, not from MLS. -/
theorem Hyps.busy_step (H : Hyps P R δ ω home follows x v s) {k : ℕ}
    (hbusy : (s k).busy = true) (hnot : k < (s k).start + P.steps) :
    s (k + 1) = { s k with age := (s k).age + 1 } := by
  have hI := H.inv k
  have hstep := H.run.2 k
  generalize s (k + 1) = st' at hstep ⊢
  cases hstep with
  | finish _ hdue _ => have := (H.due_iff _ k).mp hdue; omega
  | timeout _ _ hage =>
    have := (hI.busy_spec hbusy).2.2
    have := H.ceil_le_bound
    unfold Params.steps at *; omega
  | tick => rfl
  | wait h => simp [hbusy] at h
  | admit _ h => simp [hbusy] at h

/-- **Finish on time (conclusion (b)).** A move admitted at boundary `k₀` (idle at `k₀`, busy after
it) is busy with age `j` and the same goal after each boundary `k₀ + j` with `j < ⌈T/h⌉`, and is
finished at boundary `k₀ + ⌈T/h⌉`: after it the loop is idle with the arm at the goal. With
`⌈T/h⌉ ≤ bound`, the age stays below the bound, so the move never times out. A design statement,
not from MLS. -/
theorem Hyps.finish_on_time (H : Hyps P R δ ω home follows x v s) {k₀ : ℕ}
    (hidle : (s k₀).busy = false) (hbusy : (s (k₀ + 1)).busy = true) :
    (∀ j, j < P.steps → (s (k₀ + 1 + j)).busy = true ∧ (s (k₀ + 1 + j)).age = j ∧
        (s (k₀ + 1 + j)).goal = (s (k₀ + 1)).goal ∧ (s (k₀ + 1 + j)).start = k₀) ∧
      (s (k₀ + P.steps + 1)).busy = false ∧
      (s (k₀ + P.steps + 1)).current = (s (k₀ + 1)).goal := by
  obtain ⟨-, -, hstart, hage⟩ := H.admit_spec hidle hbusy
  have hpos := H.steps_pos
  have hbusyj : ∀ j, j < P.steps → (s (k₀ + 1 + j)).busy = true ∧ (s (k₀ + 1 + j)).age = j ∧
      (s (k₀ + 1 + j)).goal = (s (k₀ + 1)).goal ∧ (s (k₀ + 1 + j)).start = k₀ := by
    intro j
    induction j with
    | zero => intro _; exact ⟨hbusy, hage, rfl, hstart⟩
    | succ j ih =>
      intro hj
      obtain ⟨hb, ha, hg, hs⟩ := ih (by omega)
      have hnext := H.busy_step (k := k₀ + 1 + j) hb (by omega)
      rw [show k₀ + 1 + (j + 1) = k₀ + 1 + j + 1 by ring, hnext]
      exact ⟨hb, by simp [ha], hg, hs⟩
  refine ⟨hbusyj, ?_⟩
  obtain ⟨hb, -, hg, hs⟩ := hbusyj (P.steps - 1) (by omega)
  have hk : k₀ + 1 + (P.steps - 1) = k₀ + P.steps := by omega
  rw [hk] at hb hg hs
  have hI := H.inv (k₀ + P.steps)
  have hstep := H.run.2 (k₀ + P.steps)
  have hdue : Due P (s (k₀ + P.steps)) (k₀ + P.steps) :=
    (H.due_iff _ _).mpr (by rw [hs])
  have hp := H.period_pos
  have hkle : (((s (k₀ + P.steps)).start : ℕ) : ℝ) * P.period ≤
      ((k₀ + P.steps : ℕ) : ℝ) * P.period :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hI.start_le) hp.le
  have htube := H.tube_of_inv hI ⟨hkle, le_rfl⟩
  have hrest := R.rest (a := P.pos (s (k₀ + P.steps)).src) (b := P.pos (s (k₀ + P.steps)).goal)
    (t₀ := (s (k₀ + P.steps)).start * P.period) (t := ((k₀ + P.steps : ℕ) : ℝ) * P.period)
    (Or.inr hdue)
  rw [hrest.1, hrest.2] at htube
  have harr := H.arrived_of_inTube htube
  generalize s (k₀ + P.steps + 1) = st' at hstep ⊢
  cases hstep with
  | finish => exact ⟨rfl, hg⟩
  | timeout _ hnot => exact absurd ⟨hdue, harr⟩ hnot
  | tick _ hnot => exact absurd ⟨hdue, harr⟩ hnot
  | wait h => simp [hb] at h
  | admit _ h => simp [hb] at h

/-- **The assured loop.** Along every timed run of the sampled loop and every motion under the
standing hypotheses `Hyps` (policy, tracking of the last admitted move, the move corollary, the
tube around home at time `0`, `0 < h`, `0 < T`, `⌈T/h⌉ ≤ bound`, `0 ≤ ω`, `δ ≤ δ_a`,
`2 ω δ ≤ v_a`, home linked to itself), with cells certified at an inflation `δ_c ≥ δ` and a tool
map with the Lipschitz-type bound `L`:
(a) the configuration is clear at every instant `t ≥ 0`;
(b) the supervisor is never faulted, the age stays below the bound, and a move admitted at
boundary `k₀` is finished at boundary `k₀ + ⌈T/h⌉` with the arm at its goal;
(c) at each finish the tool is within `L δ` of the goal's tool position;
(d) at each finish the motion is in the tube around the goal at rest.
A design statement, not from MLS. -/
theorem Hyps.assured {E : Type*} [PseudoMetricSpace E] (H : Hyps P R δ ω home follows x v s)
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
  ⟨fun _ ht => H.clear hcert hδ ht,
   fun k => ⟨H.faulted_eq_false k, H.age_lt_bound k⟩,
   fun _ hidle hbusy => by
     obtain ⟨h1, h2, h3⟩ := H.finish_on_time hidle hbusy
     exact ⟨fun j hj => (h1 j hj).1, h2, h3⟩,
   fun _ hbusy hidle => H.tool_dist_of_finish htool hbusy hidle,
   fun _ hbusy hidle => H.tube_of_finish hbusy hidle⟩

end RoboLean.Cell.Loop
