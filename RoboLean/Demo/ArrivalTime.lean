import RoboLean.Demo.SupervisorRefines
import RoboLean.Examples.PlanarTwoLinkRegulation

/-!
# Arrival times for the planar arm demo in the ideal continuous model

The executable supervisor (`RoboLean.Demo.Supervisor`) commands targets; by the refinement
(`RoboLean.Demo.SupervisorRefines`) every commanded target `(x, y)` is the end-effector point
`planarArmXY a b θ_d = (x, y)` of the elbow-down joint vector `θ_d = elbowDown a b x y` of MLS
eq. (3.16), printed p. 98 (`setPoint`). This file joins that fact to a quantitative convergence
statement for the ideal arm held at the set point `θ_d` from the time `t₀` of the command:

* **hypothesis structure.** The closed loop has an exponential bound with named constants
  `(C, α)` at `(θ_d, 0)` on the initial state errors smaller than `ρ`
  (`Stability.ExponentialBoundOn`, MLS Definition 4.3, p. 180);
* **position error.** Then the end-effector error at time `t ≥ t₀` is at most
  `(a + 2b) C e^{−α(t − t₀)} ‖(θ(t₀) − θ_d, θ̇(t₀))‖` (`planarDist_le_of_run`), the factor
  `a + 2b` being the Lipschitz constant of `planarArmXY` (`Examples.planarDist_planarArmXY_le`);
* **arrival time.** Hence the end effector is within `ε` of the target at every time `t` with
  `t − t₀ ≥ T* = arrivalTime C α ρ (ε / (a + 2b))` (`planarDist_le_of_arrivalTime_le_of_run`),
  and at every sample `t₀ + k h` with `k h ≥ T*` (`planarDist_le_at_sample_of_run`);
* **design statement.** If the period `h` times the age bound is at least `T*`, the end effector is
  within `ε` of every commanded target at the sample taken when the age bound is reached
  (`planarDist_le_at_bound_of_run`); the demo's loop tests arrival at every period boundary before
  it ticks and times a command out one period after its age reaches the bound, so in the ideal
  model such a command finishes at that sample or earlier;
* **discharged constants.** For the planar arm with positive masses and principal moments under
  the PD law with `K_p = K_v = I` (the demo's gains), constants exist for every `ρ`, uniformly in
  the set point (`exists_arrival_of_run`): one `C` and, for each `ρ`, one `α`, and then, for every
  tolerance and period, an age bound that certifies arrival (`exists_bound_arrival_of_run`). Their
  values are not computed here; for the demo's own parameters `RoboLean.Demo.ArrivalConstants`
  computes explicit ones.

The convention is the demo report's: the book's frame of `planarArmXY` (zero configuration along
`+x`, MLS Figure 4.4, p. 164), the Euclidean distance of the plane for the tolerance
(`Examples.planarDist`), the state `(θ, θ̇)` with the sup norm, and the target held fixed from `t₀`
on. Everything here concerns the ideal continuous model: not the sampled loop, the switching of
set points, the floating-point simulation, the protocol or a physical arm.
-/

noncomputable section

namespace RoboLean.Demo

open RoboLean.Examples RoboLean.Stability

/-- **The set point of a commanded target:** the elbow-down joint vector of MLS eq. (3.16),
p. 98, `elbowDown a b x y`, for the target `(x, y)` (book's frame, MLS Figure 4.4, p. 164) and
the link lengths of the parameters, cast to `ℝ`. -/
def setPoint (p : Params) (t : Target) : Fin 2 → ℝ :=
  elbowDown (p.a : ℝ) (p.b : ℝ) (t.1 : ℝ) (t.2 : ℝ)

/-- **The demo's closed loop at a set point:** the planar arm of MLS Figure 4.4 (p. 164,
`planarTwoLinkModel` with first link length `l₁`) under the PD law (4.51), p. 193, with
compensation of `N` and `K_p = K_v = I`, the demo's gains, as the field on the state `(θ, θ̇)`. -/
def armClosedLoop (m₁ m₂ r₁ r₂ l₁ : ℝ) (I₁ I₂ : Fin 3 → ℝ) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) (θd : Fin 2 → ℝ) :
    ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ) → (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  (planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).field
    ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).pdCompensatedTorque 1 1 θd)

/-- **The end-effector error of a commanded target decays exponentially (MLS eq. (3.16), p. 98,
and Definition 4.3, p. 180; the demo report's conventions).** For positive and distinct link
lengths, in every state that the executable supervisor reaches from `State.init`, for every
commanded target `(x, y)` and every closed loop `f` with an exponential bound with constants
`(C, α)` at `(setPoint p (x, y), 0)` on the initial errors smaller than `ρ`, every solution from
`t₀ ≥ 0` starting within `ρ` satisfies, for `t ≥ t₀`,
`dist(planarArmXY a b θ(t), (x, y)) ≤ (a + 2b) C e^{−α(t − t₀)} ‖x(t₀) − (θ_d, 0)‖`
(Euclidean distance, `θ(t) = (x t).1`). The ideal continuous model with the target fixed. -/
theorem planarDist_le_of_run {p : Params} {acts : List Action} {s : State} (ha : 0 < p.a)
    (hb : 0 < p.b) (hab : p.a ≠ p.b) (hrun : run p State.init acts = some s) {tgt : Target}
    (htgt : tgt ∈ s.commanded)
    {f : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ) → (Fin 2 → ℝ) × (Fin 2 → ℝ)} {C α ρ : ℝ}
    (hB : ExponentialBoundOn f (setPoint p tgt, 0) C α ρ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {x : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hx : IsSolution f t₀ x)
    (hx₀ : ‖x t₀ - (setPoint p tgt, 0)‖ < ρ) {t : ℝ} (ht : t₀ ≤ t) :
    planarDist (planarArmXY (p.a : ℝ) (p.b : ℝ) (x t).1) ![(tgt.1 : ℝ), tgt.2] ≤
      ((p.a : ℝ) + 2 * p.b) * (C * Real.exp (-α * (t - t₀)) * ‖x t₀ - (setPoint p tgt, 0)‖) := by
  have hθd : planarArmXY (p.a : ℝ) (p.b : ℝ) (setPoint p tgt) = ![(tgt.1 : ℝ), tgt.2] :=
    planarArmXY_elbowDown_of_run ha hb hab hrun tgt htgt
  have ha0 : (0 : ℝ) ≤ p.a := by exact_mod_cast ha.le
  have hb0 : (0 : ℝ) ≤ p.b := by exact_mod_cast hb.le
  have hL := planarDist_planarArmXY_le ha0 hb0 (x t).1 (setPoint p tgt)
  rw [hθd] at hL
  have hjoint : ‖(x t).1 - setPoint p tgt‖ ≤ ‖x t - (setPoint p tgt, 0)‖ :=
    norm_fst_le (x t - (setPoint p tgt, 0))
  have hbound := hB.bound t₀ ht₀ x hx hx₀ t ht
  calc planarDist (planarArmXY (p.a : ℝ) (p.b : ℝ) (x t).1) ![(tgt.1 : ℝ), tgt.2]
      ≤ ((p.a : ℝ) + 2 * p.b) * ‖(x t).1 - setPoint p tgt‖ := hL
    _ ≤ ((p.a : ℝ) + 2 * p.b) * ‖x t - (setPoint p tgt, 0)‖ := by gcongr
    _ ≤ ((p.a : ℝ) + 2 * p.b) * (C * Real.exp (-α * (t - t₀)) * ‖x t₀ - (setPoint p tgt, 0)‖) := by
        gcongr

/-- **Arrival within the tolerance after the arrival time (MLS eq. (3.16), p. 98, and Definition
4.3, p. 180; the demo report's conventions).** Under the hypotheses of `planarDist_le_of_run` and a
tolerance `ε > 0`, the end effector is within Euclidean distance `ε` of the commanded target at
every time `t` with `t − t₀ ≥ arrivalTime C α ρ (ε / (a + 2b))`. -/
theorem planarDist_le_of_arrivalTime_le_of_run {p : Params} {acts : List Action} {s : State}
    (ha : 0 < p.a) (hb : 0 < p.b) (hab : p.a ≠ p.b) (hrun : run p State.init acts = some s)
    {tgt : Target} (htgt : tgt ∈ s.commanded)
    {f : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ) → (Fin 2 → ℝ) × (Fin 2 → ℝ)} {C α ρ : ℝ}
    (hB : ExponentialBoundOn f (setPoint p tgt, 0) C α ρ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {x : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hx : IsSolution f t₀ x)
    (hx₀ : ‖x t₀ - (setPoint p tgt, 0)‖ < ρ) {ε : ℝ} (hε : 0 < ε) {t : ℝ}
    (ht : arrivalTime C α ρ (ε / ((p.a : ℝ) + 2 * p.b)) ≤ t - t₀) :
    planarDist (planarArmXY (p.a : ℝ) (p.b : ℝ) (x t).1) ![(tgt.1 : ℝ), tgt.2] ≤ ε := by
  have ha0 : (0 : ℝ) < p.a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < p.b := by exact_mod_cast hb
  have hL : (0 : ℝ) < p.a + 2 * p.b := by positivity
  have h0 : (0 : ℝ) ≤ arrivalTime C α ρ (ε / ((p.a : ℝ) + 2 * p.b)) := le_max_left _ _
  have h1 := planarDist_le_of_run ha hb hab hrun htgt hB ht₀ hx hx₀ (t := t) (by linarith)
  have h2 := mul_exp_mul_le_of_arrivalTime_le hB.pos_C hB.pos_α (div_pos hε hL) (norm_nonneg _)
    hx₀.le ht
  calc planarDist (planarArmXY (p.a : ℝ) (p.b : ℝ) (x t).1) ![(tgt.1 : ℝ), tgt.2]
      ≤ ((p.a : ℝ) + 2 * p.b) * (C * Real.exp (-α * (t - t₀)) * ‖x t₀ - (setPoint p tgt, 0)‖) :=
        h1
    _ ≤ ((p.a : ℝ) + 2 * p.b) * (ε / ((p.a : ℝ) + 2 * p.b)) := by gcongr
    _ = ε := by field_simp

/-- **The sampled arrival test passes after the arrival time (the demo report's conventions; MLS
eq. (3.16), p. 98, and Definition 4.3, p. 180).** Under the hypotheses of `planarDist_le_of_run`,
for a tolerance `ε > 0`, a period `h` and a sample index `k` with
`k h ≥ arrivalTime C α ρ (ε / (a + 2b))`, the end effector is within `ε` of the commanded target
at the sample time `t₀ + k h`. -/
theorem planarDist_le_at_sample_of_run {p : Params} {acts : List Action} {s : State}
    (ha : 0 < p.a) (hb : 0 < p.b) (hab : p.a ≠ p.b) (hrun : run p State.init acts = some s)
    {tgt : Target} (htgt : tgt ∈ s.commanded)
    {f : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ) → (Fin 2 → ℝ) × (Fin 2 → ℝ)} {C α ρ : ℝ}
    (hB : ExponentialBoundOn f (setPoint p tgt, 0) C α ρ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {x : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hx : IsSolution f t₀ x)
    (hx₀ : ‖x t₀ - (setPoint p tgt, 0)‖ < ρ) {ε : ℝ} (hε : 0 < ε) {h : ℝ} {k : ℕ}
    (hk : arrivalTime C α ρ (ε / ((p.a : ℝ) + 2 * p.b)) ≤ k * h) :
    planarDist (planarArmXY (p.a : ℝ) (p.b : ℝ) (x (t₀ + k * h)).1) ![(tgt.1 : ℝ), tgt.2] ≤ ε :=
  planarDist_le_of_arrivalTime_le_of_run ha hb hab hrun htgt hB ht₀ hx hx₀ hε
    (by rw [add_sub_cancel_left]; exact hk)

/-- **Design statement: arrival before the timeout (the demo report's conventions; MLS eq. (3.16),
p. 98, and Definition 4.3, p. 180).** Under the hypotheses of `planarDist_le_of_run`, if the period
`h` times the supervisor's age bound is at least `arrivalTime C α ρ (ε / (a + 2b))`, the end
effector is within `ε > 0` of every commanded target at the sample `t₀ + bound · h`, the sample
after which the age of the command reaches the bound; a sampled arrival test with tolerance `ε` run
at that sample passes. For the ideal continuous model with the target fixed from `t₀`; the timing
of ticks, tests and timeouts is the demo loop's policy, not part of the statement. -/
theorem planarDist_le_at_bound_of_run {p : Params} {acts : List Action} {s : State}
    (ha : 0 < p.a) (hb : 0 < p.b) (hab : p.a ≠ p.b) (hrun : run p State.init acts = some s)
    {tgt : Target} (htgt : tgt ∈ s.commanded)
    {f : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ) → (Fin 2 → ℝ) × (Fin 2 → ℝ)} {C α ρ : ℝ}
    (hB : ExponentialBoundOn f (setPoint p tgt, 0) C α ρ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {x : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hx : IsSolution f t₀ x)
    (hx₀ : ‖x t₀ - (setPoint p tgt, 0)‖ < ρ) {ε : ℝ} (hε : 0 < ε) {h : ℝ}
    (hT : arrivalTime C α ρ (ε / ((p.a : ℝ) + 2 * p.b)) ≤ p.bound * h) :
    planarDist (planarArmXY (p.a : ℝ) (p.b : ℝ) (x (t₀ + p.bound * h)).1)
      ![(tgt.1 : ℝ), tgt.2] ≤ ε :=
  planarDist_le_at_sample_of_run ha hb hab hrun htgt hB ht₀ hx hx₀ hε hT

/-- **The arrival constants exist for the demo's closed loop (MLS Proposition 4.10, p. 194, at a
constant set point; eq. (3.16), p. 98; the demo report's conventions).** For the planar arm with
positive masses and principal moments, any gravity data and joint forces, any first link length
`l₁` of the dynamic model (the demo's is `a`) and `K_p = K_v = I`, there is `C > 0` and, for every
`ρ > 0`, a rate `α > 0` such that for all parameters with positive and distinct lengths, every run
of the executable supervisor from `State.init`, every commanded target, every solution of the
closed loop at its set point from `t₀ ≥ 0` starting within `ρ`, every tolerance `ε > 0` and every
`t` with `t − t₀ ≥ arrivalTime C α ρ (ε / (a + 2b))`, the end effector is within `ε` of the target.
The dynamic model's first link length is not tied to `a`: the bound concerns the joint error and
the end-effector map `planarArmXY a b`. -/
theorem exists_arrival_of_run {m₁ m₂ r₁ r₂ l₁ : ℝ} {I₁ I₂ : Fin 3 → ℝ} (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    ∃ C > 0, ∀ ρ > 0, ∃ α > 0, ∀ (p : Params) (acts : List Action) (s : State),
      0 < p.a → 0 < p.b → p.a ≠ p.b → run p State.init acts = some s →
      ∀ tgt ∈ s.commanded, ∀ t₀, 0 ≤ t₀ → ∀ x : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ),
      IsSolution (armClosedLoop m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne (setPoint p tgt)) t₀ x →
      ‖x t₀ - (setPoint p tgt, 0)‖ < ρ → ∀ ε > 0, ∀ t,
      arrivalTime C α ρ (ε / ((p.a : ℝ) + 2 * p.b)) ≤ t - t₀ →
      planarDist (planarArmXY (p.a : ℝ) (p.b : ℝ) (x t).1) ![(tgt.1 : ℝ), tgt.2] ≤ ε := by
  obtain ⟨C, hC, H⟩ := planarTwoLinkArm_exponentialBoundOn_pdCompensatedTorque m₁ m₂ r₁ r₂ l₁
    I₁ I₂ hm₁ hm₂ hI₁ hI₂ g up Ne
  refine ⟨C, hC, fun ρ hρ => ?_⟩
  obtain ⟨α, hα, Hα⟩ := H ρ hρ
  exact ⟨α, hα, fun p acts s ha hb hab hrun tgt htgt t₀ ht₀ x hx hx₀ ε hε t ht =>
    planarDist_le_of_arrivalTime_le_of_run ha hb hab hrun htgt (Hα (setPoint p tgt)) ht₀ hx hx₀
      hε ht⟩

/-- **An age bound that certifies arrival exists (MLS Proposition 4.10, p. 194, at a constant set
point; eq. (3.16), p. 98; the demo report's conventions).** For the planar arm with positive
masses and principal moments, any gravity data and joint forces, first link length `l₁`,
`K_p = K_v = I`, every radius `ρ > 0` of initial state errors, every tolerance `ε > 0`, every
period `h > 0` and every second link length `b > 0`, there is an age bound `N₀` such that for all
parameters with `a = l₁`, `b` the given length, distinct lengths and age bound at least `N₀`, every
run of the executable supervisor, every commanded target and every solution of the closed loop at
its set point from `t₀ ≥ 0` starting within `ρ`, the end effector is within `ε` of the target at
the sample `t₀ + bound · h`. The bound `N₀` is not computed numerically. -/
theorem exists_bound_arrival_of_run {m₁ m₂ r₁ r₂ l₁ : ℝ} {I₁ I₂ : Fin 3 → ℝ} (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) {ρ ε h : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hh : 0 < h) (b : ℚ) (hb : 0 < b) :
    ∃ N₀ : ℕ, ∀ (p : Params) (acts : List Action) (s : State),
      (p.a : ℝ) = l₁ → p.b = b → 0 < p.a → p.a ≠ p.b → N₀ ≤ p.bound →
      run p State.init acts = some s →
      ∀ tgt ∈ s.commanded, ∀ t₀, 0 ≤ t₀ → ∀ x : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ),
      IsSolution (armClosedLoop m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne (setPoint p tgt)) t₀ x →
      ‖x t₀ - (setPoint p tgt, 0)‖ < ρ →
      planarDist (planarArmXY (p.a : ℝ) (p.b : ℝ) (x (t₀ + p.bound * h)).1)
        ![(tgt.1 : ℝ), tgt.2] ≤ ε := by
  obtain ⟨C, hC, H⟩ := planarTwoLinkArm_exponentialBoundOn_pdCompensatedTorque m₁ m₂ r₁ r₂ l₁
    I₁ I₂ hm₁ hm₂ hI₁ hI₂ g up Ne
  obtain ⟨α, hα, Hα⟩ := H ρ hρ
  set T := arrivalTime C α ρ (ε / (l₁ + 2 * (b : ℝ))) with hTdef
  refine ⟨⌈T / h⌉₊, fun p acts s hl hpb ha hab hN hrun tgt htgt t₀ ht₀ x hx hx₀ => ?_⟩
  have hb' : 0 < p.b := hpb ▸ hb
  have hT1 : T ≤ (⌈T / h⌉₊ : ℝ) * h := (div_le_iff₀ hh).mp (Nat.le_ceil _)
  have hT2 : (⌈T / h⌉₊ : ℝ) * h ≤ p.bound * h := by gcongr
  have hT : arrivalTime C α ρ (ε / ((p.a : ℝ) + 2 * p.b)) ≤ p.bound * h := by
    rw [hl, hpb]
    exact hT1.trans hT2
  exact planarDist_le_at_bound_of_run ha hb' hab hrun htgt (Hα (setPoint p tgt)) ht₀ hx hx₀ hε hT

end RoboLean.Demo
