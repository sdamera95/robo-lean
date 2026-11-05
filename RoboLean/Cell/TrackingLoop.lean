import RoboLean.Cell.ArmInertia
import RoboLean.Cell.Loop

/-!
# The tracking tube as the loop's move corollary

A design statement, not from MLS. The sampled loop of `RoboLean.Cell.Loop` takes the plant as an
abstract hypothesis, `Loop.MoveCorollary`: for every linked move, on every finite horizon
`[t₀, t₁]` with `0 ≤ t₀`, a motion that obeys a tracking predicate `follows a b t₀ t` at every
`t ∈ (t₀, t₁]` and starts in the tube around the start waypoint at rest stays in the tube around
the move reference. This file discharges it for computed torque (MLS eq. (4.49), p. 191, along a
motion as on p. 301) under a bounded disturbance torque.

**Formalized.**

* `quinticMoveRef`: the clamped quintic reference `moveRef` as the loop's `Loop.MoveRef`.
* `loop_inTube_iff`: the loop's tube `Loop.InTube δ ω r r' θ θ'` is `InTube ω δ θ θ' r r'`.
* `FollowsAt`: at time `t` the motion `x` has velocity `v` and acceleration `acc`, the inertia
  curve satisfies the bound `m₀ ‖w‖₂² ≤ wᵀ M(t) w` when every joint is within `η` of the
  reference, the disturbance satisfies `‖d(t)‖₂ ≤ d̄`, and the disturbed computed-torque equation
  holds with the reference of the move from `a` to `b` admitted at `t₀`;
  `moveCorollary_of_followsAt` gives `Loop.MoveCorollary` from it.
* `CellArmFollowsAt` and `cellArm_moveCorollary`, `cellArm_moveCorollary_global`: the same for
  the cell arm's equations of motion, with the inertia bound discharged by
  `cellArm_inertia_lower_of_reach` (every configuration within `η` of the segment between linked
  waypoints keeps the forearm's mass centre at horizontal distance at least `1/8` m from the base
  axis) or by the global bound `cellArm_inertia_lower`.

* `FollowsAccelAt`, `moveCorollary_of_followsAccelAt`, `CellArmFollowsAccelAt` and
  `cellArm_moveCorollary_accel`: the same with the disturbance bounded at the acceleration level
  (`|(M⁻¹ d)ᵢ| ≤ ω² δ`), without an inertia constant or a joint range.

A standing hypothesis of the bridge is that `(x, v)` is continuous on `[0, ∞)`; the predicate
`follows` is pointwise in time and gives continuity only on `(t₀, t₁]`. Conventions as in
`RoboLean.Cell.Tracking`: joint vectors `Fin n → ℝ` in radians, time in seconds, the Euclidean
norm through `w ⬝ᵥ w`, per-joint tube bounds.
-/

noncomputable section

open Matrix Set

namespace RoboLean
namespace Cell

variable {n : ℕ}

/-- **The clamped quintic move reference as the loop's move-reference interface (a design
statement, not from MLS):** positions `moveRef a b t₀ T t`, velocities `moveRefDeriv a b t₀ T t`,
for a duration `T > 0` (seconds). -/
def quinticMoveRef {T : ℝ} (hT : 0 < T) : Loop.MoveRef n T where
  pos a b t₀ t := moveRef a b t₀ T t
  vel a b t₀ t := moveRefDeriv a b t₀ T t
  pos_mem_segment a b t₀ t := moveRef_mem_segment a b t₀ T t
  pos_of_le _ _ _ _ h := moveRef_of_ge hT h
  vel_of_le _ _ _ _ h := moveRefDeriv_of_ge hT h
  vel_self a t₀ t := moveRefDeriv_self a t₀ T t

/-- **The loop's tube is the tracking tube (a design statement, not from MLS):**
`Loop.InTube δ ω r r' θ θ'` and `InTube ω δ θ θ' r r'` are the same per-joint condition. -/
theorem loop_inTube_iff {δ ω : ℝ} {r r' θ θ' : Fin n → ℝ} :
    Loop.InTube δ ω r r' θ θ' ↔ InTube ω δ θ θ' r r' :=
  Iff.rfl

/-- **The motion follows the move reference at time `t` (a design statement, not from MLS; the
law is MLS eq. (4.49), p. 191, along a motion as on p. 301).** For the move from `a` to `b`
admitted at `t₀` with duration `T`: `x` has velocity `v t` and `v` has acceleration `acc t` at
`t`; if every joint is within `η` of the reference then `m₀ ‖w‖₂² ≤ wᵀ M(t) w` for every `w`;
`‖d(t)‖₂ ≤ d̄` (as `d ⬝ᵥ d ≤ d̄²`); and `M ẍ + C ẋ + N = F(t) + d(t)` with the computed torque `F`
for the gains `ω² I`, `2ω I` and the reference `moveRef a b t₀ T`. -/
def FollowsAt (ω T m₀ η dbar : ℝ) (Mt Ct : ℝ → Matrix (Fin n) (Fin n) ℝ) (Nt : ℝ → Fin n → ℝ)
    (x v acc d : ℝ → Fin n → ℝ) (a b : Fin n → ℝ) (t₀ t : ℝ) : Prop :=
  HasDerivAt x (v t) t ∧ HasDerivAt v (acc t) t ∧
    ((∀ i, |x t i - moveRef a b t₀ T t i| ≤ η) → ∀ w, m₀ * (w ⬝ᵥ w) ≤ w ⬝ᵥ (Mt t *ᵥ w)) ∧
    d t ⬝ᵥ d t ≤ dbar ^ 2 ∧
    Mt t *ᵥ acc t + Ct t *ᵥ v t + Nt t =
      Control.computedTorqueAlong ((ω ^ 2) • 1) ((2 * ω) • 1) (Mt t) (Ct t) (Nt t)
        (moveRef a b t₀ T t) (moveRefDeriv a b t₀ T t) (moveRefDeriv2 a b t₀ T t) (x t) (v t) +
        d t

/-- **The loop's move corollary for disturbed computed torque (a design statement, not from
MLS; `move_tube`).** With `ω > 0`, `m₀ > 0`, `δ < η`, `0 ≤ d̄ ≤ m₀ ω² δ`, a move duration
`T > 0` and `(x, v)` continuous on `[0, ∞)`, the motion satisfies `Loop.MoveCorollary` for the
quintic reference and the tracking predicate `FollowsAt`. -/
theorem moveCorollary_of_followsAt {W : Type*} (P : Loop.Params n W) (hT : 0 < P.duration)
    {ω δ η m₀ dbar : ℝ} (hω : 0 < ω) (hm₀ : 0 < m₀) (hδη : δ < η) (hdbar₀ : 0 ≤ dbar)
    (hdbar : dbar ≤ m₀ * ω ^ 2 * δ) {Mt Ct : ℝ → Matrix (Fin n) (Fin n) ℝ} {Nt : ℝ → Fin n → ℝ}
    {x v acc d : ℝ → Fin n → ℝ} (hc : ContinuousOn (fun s => (x s, v s)) (Ici 0)) :
    Loop.MoveCorollary P (quinticMoveRef hT) δ ω
      (fun a b t₀ t => FollowsAt ω P.duration m₀ η dbar Mt Ct Nt x v acc d (P.pos a) (P.pos b)
        t₀ t) x v := by
  intro a b _ t₀ t₁ ht₀ _ hf h₀ t ht
  exact ((move_tube hω hm₀ hδη hdbar₀ hdbar hT (hc.mono fun s hs => ht₀.trans hs.1)
    (fun s hs => (hf s hs).1) (fun s hs => (hf s hs).2.1) (fun s hs => (hf s hs).2.2.1)
    (fun s hs => (hf s hs).2.2.2.1) (fun s hs => (hf s hs).2.2.2.2) h₀).1 t ht).1

/-- **The cell arm follows the move reference at time `t` (a design statement, not from MLS;
computed torque of MLS eq. (4.49), p. 191, for the robot of p. 303).** `x` has velocity `v t`
and `v` has acceleration `acc t` at `t`, `‖d(t)‖₂ ≤ d̄`, and the arm's equations of motion
`M ẍ + C ẋ + N = F + d` hold at `t` with the robot's computed torque `F` for the gains `ω² I`,
`2ω I` and the reference of the move from `a` to `b` admitted at `t₀` with duration `T`. -/
def CellArmFollowsAt (ω T dbar : ℝ) (x v acc d : ℝ → Fin 3 → ℝ) (a b : Fin 3 → ℝ)
    (t₀ t : ℝ) : Prop :=
  HasDerivAt x (v t) t ∧ HasDerivAt v (acc t) t ∧ d t ⬝ᵥ d t ≤ dbar ^ 2 ∧
    cellRobot.M (x t) *ᵥ acc t + cellRobot.C (x t) (v t) *ᵥ v t + cellRobot.N (x t) (v t) =
      cellRobot.computedTorque ((ω ^ 2) • 1) ((2 * ω) • 1) (moveRef a b t₀ T)
        (moveRefDeriv a b t₀ T) (moveRefDeriv2 a b t₀ T) t (x t) (v t) + d t

/-- **The loop's move corollary for the cell arm (a design statement, not from MLS).** With
`ω > 0`, `δ < η`, `0 ≤ d̄ ≤ (9/100) ω² δ`, a move duration `T > 0`, `(x, v)` continuous on
`[0, ∞)`, and every configuration within `η` (each joint) of a point of the segment between two
linked waypoints keeping the forearm's mass centre at horizontal distance at least `1/8` m from
the base axis, the arm's motion satisfies `Loop.MoveCorollary` for the quintic reference and the
tracking predicate `CellArmFollowsAt`. -/
theorem cellArm_moveCorollary {W : Type*} (P : Loop.Params 3 W) (hT : 0 < P.duration)
    {ω δ η dbar : ℝ} (hω : 0 < ω) (hδη : δ < η) (hdbar₀ : 0 ≤ dbar)
    (hdbar : dbar ≤ 9 / 100 * ω ^ 2 * δ)
    (hreach : ∀ a b, P.linked a b → ∀ p ∈ segment ℝ (P.pos a) (P.pos b), ∀ θ : Fin 3 → ℝ,
      (∀ i, |θ i - p i| ≤ η) → 1 / 8 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2))
    {x v acc d : ℝ → Fin 3 → ℝ} (hc : ContinuousOn (fun s => (x s, v s)) (Ici 0)) :
    Loop.MoveCorollary P (quinticMoveRef hT) δ ω
      (fun a b t₀ t => CellArmFollowsAt ω P.duration dbar x v acc d (P.pos a) (P.pos b) t₀ t)
      x v := by
  intro a b hab t₀ t₁ ht₀ _ hf h₀ t ht
  exact ((cellArm_move_tube hω hδη hdbar₀ hdbar hT
    (fun s _ θ hθ => hreach a b hab _ (moveRef_mem_segment _ _ _ _ _) θ hθ)
    (hc.mono fun s hs => ht₀.trans hs.1) (fun s hs => (hf s hs).1) (fun s hs => (hf s hs).2.1)
    (fun s hs => (hf s hs).2.2.1) (fun s hs => (hf s hs).2.2.2) h₀).1 t ht).1

/-- **The loop's move corollary for the cell arm with the global inertia bound (a design
statement, not from MLS):** as `cellArm_moveCorollary` without a joint-range hypothesis, under
the smaller disturbance budget `0 ≤ d̄ ≤ (3/100) ω² δ`. -/
theorem cellArm_moveCorollary_global {W : Type*} (P : Loop.Params 3 W) (hT : 0 < P.duration)
    {ω δ dbar : ℝ} (hω : 0 < ω) (hdbar₀ : 0 ≤ dbar) (hdbar : dbar ≤ 3 / 100 * ω ^ 2 * δ)
    {x v acc d : ℝ → Fin 3 → ℝ} (hc : ContinuousOn (fun s => (x s, v s)) (Ici 0)) :
    Loop.MoveCorollary P (quinticMoveRef hT) δ ω
      (fun a b t₀ t => CellArmFollowsAt ω P.duration dbar x v acc d (P.pos a) (P.pos b) t₀ t)
      x v := by
  intro a b _ t₀ t₁ ht₀ _ hf h₀ t ht
  exact ((cellArm_move_tube_global hω hdbar₀ hdbar hT (hc.mono fun s hs => ht₀.trans hs.1)
    (fun s hs => (hf s hs).1) (fun s hs => (hf s hs).2.1) (fun s hs => (hf s hs).2.2.1)
    (fun s hs => (hf s hs).2.2.2) h₀).1 t ht).1

/-- **The motion follows the move reference at time `t`, with the disturbance bounded at the
acceleration level (a design statement, not from MLS; the law is MLS eq. (4.49), p. 191, along a
motion as on p. 301).** As `FollowsAt`, with the inertia and torque bounds replaced by: every `w`
with `M(t) w = d(t)` satisfies `|wᵢ| ≤ ω² δ` for every joint (rad/s²). -/
def FollowsAccelAt (ω T δ : ℝ) (Mt Ct : ℝ → Matrix (Fin n) (Fin n) ℝ) (Nt : ℝ → Fin n → ℝ)
    (x v acc d : ℝ → Fin n → ℝ) (a b : Fin n → ℝ) (t₀ t : ℝ) : Prop :=
  HasDerivAt x (v t) t ∧ HasDerivAt v (acc t) t ∧
    (∀ w, Mt t *ᵥ w = d t → ∀ i, |w i| ≤ ω ^ 2 * δ) ∧
    Mt t *ᵥ acc t + Ct t *ᵥ v t + Nt t =
      Control.computedTorqueAlong ((ω ^ 2) • 1) ((2 * ω) • 1) (Mt t) (Ct t) (Nt t)
        (moveRef a b t₀ T t) (moveRefDeriv a b t₀ T t) (moveRefDeriv2 a b t₀ T t) (x t) (v t) +
        d t

/-- **The loop's move corollary for computed torque with the disturbance bounded at the
acceleration level (a design statement, not from MLS; `move_tube_accel`).** With `ω > 0`, a
move duration `T > 0` and `(x, v)` continuous on `[0, ∞)`, the motion satisfies
`Loop.MoveCorollary` for the quintic reference and the tracking predicate `FollowsAccelAt`. -/
theorem moveCorollary_of_followsAccelAt {W : Type*} (P : Loop.Params n W) (hT : 0 < P.duration)
    {ω δ : ℝ} (hω : 0 < ω) {Mt Ct : ℝ → Matrix (Fin n) (Fin n) ℝ} {Nt : ℝ → Fin n → ℝ}
    {x v acc d : ℝ → Fin n → ℝ} (hc : ContinuousOn (fun s => (x s, v s)) (Ici 0)) :
    Loop.MoveCorollary P (quinticMoveRef hT) δ ω
      (fun a b t₀ t => FollowsAccelAt ω P.duration δ Mt Ct Nt x v acc d (P.pos a) (P.pos b) t₀ t)
      x v := by
  intro a b _ t₀ t₁ ht₀ _ hf h₀ t ht
  exact ((move_tube_accel hω hT (hc.mono fun s hs => ht₀.trans hs.1)
    (fun s hs => (hf s hs).1) (fun s hs => (hf s hs).2.1) (fun s hs => (hf s hs).2.2.1)
    (fun s hs => (hf s hs).2.2.2) h₀).1 t ht).1

/-- **The cell arm follows the move reference at time `t`, with the disturbance bounded at the
acceleration level (a design statement, not from MLS; computed torque of MLS eq. (4.49), p. 191,
for the robot of p. 303).** As `CellArmFollowsAt`, with the torque bound replaced by
`|(M(x(t))⁻¹ d(t))ᵢ| ≤ ω² δ` for every joint (rad/s²). -/
def CellArmFollowsAccelAt (ω T δ : ℝ) (x v acc d : ℝ → Fin 3 → ℝ) (a b : Fin 3 → ℝ)
    (t₀ t : ℝ) : Prop :=
  HasDerivAt x (v t) t ∧ HasDerivAt v (acc t) t ∧
    (∀ i, |((cellRobot.M (x t))⁻¹ *ᵥ d t) i| ≤ ω ^ 2 * δ) ∧
    cellRobot.M (x t) *ᵥ acc t + cellRobot.C (x t) (v t) *ᵥ v t + cellRobot.N (x t) (v t) =
      cellRobot.computedTorque ((ω ^ 2) • 1) ((2 * ω) • 1) (moveRef a b t₀ T)
        (moveRefDeriv a b t₀ T) (moveRefDeriv2 a b t₀ T) t (x t) (v t) + d t

/-- **The loop's move corollary for the cell arm with the disturbance bounded at the
acceleration level (a design statement, not from MLS; `cellArm_move_tube_accel`).** With `ω > 0`,
a move duration `T > 0` and `(x, v)` continuous on `[0, ∞)`, the arm's motion satisfies
`Loop.MoveCorollary` for the quintic reference and the tracking predicate
`CellArmFollowsAccelAt`; no joint range and no inertia constant enter. -/
theorem cellArm_moveCorollary_accel {W : Type*} (P : Loop.Params 3 W) (hT : 0 < P.duration)
    {ω δ : ℝ} (hω : 0 < ω) {x v acc d : ℝ → Fin 3 → ℝ}
    (hc : ContinuousOn (fun s => (x s, v s)) (Ici 0)) :
    Loop.MoveCorollary P (quinticMoveRef hT) δ ω
      (fun a b t₀ t => CellArmFollowsAccelAt ω P.duration δ x v acc d (P.pos a) (P.pos b) t₀ t)
      x v := by
  intro a b _ t₀ t₁ ht₀ _ hf h₀ t ht
  exact ((cellArm_move_tube_accel hω hT (hc.mono fun s hs => ht₀.trans hs.1)
    (fun s hs => (hf s hs).1) (fun s hs => (hf s hs).2.1) (fun s hs => (hf s hs).2.2.1)
    (fun s hs => (hf s hs).2.2.2) h₀).1 t ht).1

end Cell
end RoboLean
