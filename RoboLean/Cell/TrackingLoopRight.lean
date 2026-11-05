import RoboLean.Cell.TrackingMoveRight
import RoboLean.Cell.TrackingLoop

/-!
# The loop's move corollary with the acceleration required only from the right

A design statement, not from MLS. The tracking predicates of `RoboLean.Cell.TrackingLoop` in the
acceleration-level form ask for a two-sided derivative of the velocity at every instant, which a
disturbance that jumps (Coulomb friction when a joint reverses, a torque held between samples)
does not allow. Here the position and the velocity are required to have right derivatives only
(`HasDerivWithinAt f f' (Ici t) t`), and the loop's abstract plant hypothesis
`Loop.MoveCorollary` is discharged for these weaker predicates. The law is computed torque, MLS
eq. (4.49), p. 191, along a motion as on p. 301 (for the cell arm, the robot of p. 303).

**Formalized.**

* `FollowsAccelRightAt`, `FollowsAccelAt.right` (every motion that satisfies `FollowsAccelAt`
  satisfies it) and `moveCorollary_of_followsAccelRightAt`.
* `CellArmFollowsAccelRightAt`, `CellArmFollowsAccelAt.right`, the tube along a move for the cell
  arm `cellArm_move_tube_accel_right` and the move corollary `cellArm_moveCorollary_accel_right`.

At an instant where the acceleration jumps, the predicate asks the equation of motion with the
acceleration from the right, so the disturbance's value there is the one it takes just after the
jump. A standing hypothesis of the bridge is that `(x, v)` is continuous on `[0, ∞)`.
Conventions as in `RoboLean.Cell.TrackingLoop`: joint vectors `Fin n → ℝ` in radians, time in
seconds, per-joint tube bounds, the disturbance bounded at the acceleration level in rad/s².
-/

noncomputable section

open Matrix Set

namespace RoboLean
namespace Cell

variable {n : ℕ}

/-- **The motion follows the move reference at time `t`, with the disturbance bounded at the
acceleration level and right derivatives (a design statement, not from MLS; the law is MLS
eq. (4.49), p. 191, along a motion as on p. 301).** For the move from `a` to `b` admitted at
`t₀` with duration `T`: `x` has right derivative `v t` and `v` has right derivative `acc t` at
`t` (within `[t, ∞)`); every `w` with `M(t) w = d(t)` satisfies `|wᵢ| ≤ ω² δ` for every joint
(rad/s²); and `M ẍ + C ẋ + N = F(t) + d(t)` with `ẍ = acc t` and the computed torque `F` for the
gains `ω² I`, `2ω I` and the reference `moveRef a b t₀ T`. -/
def FollowsAccelRightAt (ω T δ : ℝ) (Mt Ct : ℝ → Matrix (Fin n) (Fin n) ℝ) (Nt : ℝ → Fin n → ℝ)
    (x v acc d : ℝ → Fin n → ℝ) (a b : Fin n → ℝ) (t₀ t : ℝ) : Prop :=
  HasDerivWithinAt x (v t) (Ici t) t ∧ HasDerivWithinAt v (acc t) (Ici t) t ∧
    (∀ w, Mt t *ᵥ w = d t → ∀ i, |w i| ≤ ω ^ 2 * δ) ∧
    Mt t *ᵥ acc t + Ct t *ᵥ v t + Nt t =
      Control.computedTorqueAlong ((ω ^ 2) • 1) ((2 * ω) • 1) (Mt t) (Ct t) (Nt t)
        (moveRef a b t₀ T t) (moveRefDeriv a b t₀ T t) (moveRefDeriv2 a b t₀ T t) (x t) (v t) +
        d t

/-- **The two-sided tracking predicate implies the one-sided one (a design statement, not from
MLS):** a two-sided derivative is a right derivative, so every motion that satisfies
`FollowsAccelAt` at `t` satisfies `FollowsAccelRightAt` at `t`. -/
theorem FollowsAccelAt.right {ω T δ : ℝ} {Mt Ct : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {Nt : ℝ → Fin n → ℝ} {x v acc d : ℝ → Fin n → ℝ} {a b : Fin n → ℝ} {t₀ t : ℝ}
    (h : FollowsAccelAt ω T δ Mt Ct Nt x v acc d a b t₀ t) :
    FollowsAccelRightAt ω T δ Mt Ct Nt x v acc d a b t₀ t :=
  ⟨h.1.hasDerivWithinAt, h.2.1.hasDerivWithinAt, h.2.2.1, h.2.2.2⟩

/-- **The loop's move corollary for computed torque with the disturbance bounded at the
acceleration level and right derivatives (a design statement, not from MLS;
`move_tube_accel_right`).** With `ω > 0`, a move duration `T > 0` and `(x, v)` continuous on
`[0, ∞)`, the motion satisfies `Loop.MoveCorollary` for the quintic reference and the tracking
predicate `FollowsAccelRightAt`. -/
theorem moveCorollary_of_followsAccelRightAt {W : Type*} (P : Loop.Params n W)
    (hT : 0 < P.duration) {ω δ : ℝ} (hω : 0 < ω) {Mt Ct : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {Nt : ℝ → Fin n → ℝ} {x v acc d : ℝ → Fin n → ℝ}
    (hc : ContinuousOn (fun s => (x s, v s)) (Ici 0)) :
    Loop.MoveCorollary P (quinticMoveRef hT) δ ω
      (fun a b t₀ t =>
        FollowsAccelRightAt ω P.duration δ Mt Ct Nt x v acc d (P.pos a) (P.pos b) t₀ t)
      x v := by
  intro a b _ t₀ t₁ ht₀ _ hf h₀ t ht
  exact ((move_tube_accel_right hω hT (hc.mono fun s hs => ht₀.trans hs.1)
    (fun s hs => (hf s hs).1) (fun s hs => (hf s hs).2.1) (fun s hs => (hf s hs).2.2.1)
    (fun s hs => (hf s hs).2.2.2) h₀).1 t ht).1

/-- **The cell arm follows the move reference at time `t`, with the disturbance bounded at the
acceleration level and right derivatives (a design statement, not from MLS; computed torque of
MLS eq. (4.49), p. 191, for the robot of p. 303).** `x` has right derivative `v t` and `v` has
right derivative `acc t` at `t` (within `[t, ∞)`); `|(M(x(t))⁻¹ d(t))ᵢ| ≤ ω² δ` for every joint
(rad/s²); and the arm's equations of motion `M ẍ + C ẋ + N = F + d` hold at `t` with `ẍ = acc t`
and the robot's computed torque `F` for the gains `ω² I`, `2ω I` and the reference of the move
from `a` to `b` admitted at `t₀` with duration `T`. -/
def CellArmFollowsAccelRightAt (ω T δ : ℝ) (x v acc d : ℝ → Fin 3 → ℝ) (a b : Fin 3 → ℝ)
    (t₀ t : ℝ) : Prop :=
  HasDerivWithinAt x (v t) (Ici t) t ∧ HasDerivWithinAt v (acc t) (Ici t) t ∧
    (∀ i, |((cellRobot.M (x t))⁻¹ *ᵥ d t) i| ≤ ω ^ 2 * δ) ∧
    cellRobot.M (x t) *ᵥ acc t + cellRobot.C (x t) (v t) *ᵥ v t + cellRobot.N (x t) (v t) =
      cellRobot.computedTorque ((ω ^ 2) • 1) ((2 * ω) • 1) (moveRef a b t₀ T)
        (moveRefDeriv a b t₀ T) (moveRefDeriv2 a b t₀ T) t (x t) (v t) + d t

/-- **The two-sided tracking predicate of the cell arm implies the one-sided one (a design
statement, not from MLS):** every motion that satisfies `CellArmFollowsAccelAt` at `t` satisfies
`CellArmFollowsAccelRightAt` at `t`, so every motion covered by the two-sided form is covered by
the one-sided form. -/
theorem CellArmFollowsAccelAt.right {ω T δ : ℝ} {x v acc d : ℝ → Fin 3 → ℝ} {a b : Fin 3 → ℝ}
    {t₀ t : ℝ} (h : CellArmFollowsAccelAt ω T δ x v acc d a b t₀ t) :
    CellArmFollowsAccelRightAt ω T δ x v acc d a b t₀ t :=
  ⟨h.1.hasDerivWithinAt, h.2.1.hasDerivWithinAt, h.2.2.1, h.2.2.2⟩

/-- **The tube along a move for the cell arm with the disturbance bounded at the acceleration
level and right derivatives (a design statement, not from MLS; computed torque of MLS eq. (4.49),
p. 191, for the robot of p. 303).** The conclusion of `cellArm_move_tube_accel` for a motion of
`cellRobot` with `(x, x')` continuous on `[t₀, t₁]` and, at every `s ∈ (t₀, t₁]`, right
derivatives `x'(s)` of `x` and `x''(s)` of `x'`, the equations of motion `M ẍ + C ẋ + N = F + d`
with `ẍ = x''(s)`, and `|(M(x(s))⁻¹ d(s))ᵢ| ≤ ω² δ` for every joint (rad/s²); no joint range and
no inertia constant enter. -/
theorem cellArm_move_tube_accel_right {ω δ t₀ t₁ T : ℝ} (hω : 0 < ω) (hT : 0 < T)
    {a b : Fin 3 → ℝ} {x x' x'' d : ℝ → Fin 3 → ℝ}
    (hc : ContinuousOn (fun s => (x s, x' s)) (Icc t₀ t₁))
    (hx : ∀ s ∈ Ioc t₀ t₁, HasDerivWithinAt x (x' s) (Ici s) s)
    (hx' : ∀ s ∈ Ioc t₀ t₁, HasDerivWithinAt x' (x'' s) (Ici s) s)
    (hacc : ∀ s ∈ Ioc t₀ t₁, ∀ i, |((cellRobot.M (x s))⁻¹ *ᵥ d s) i| ≤ ω ^ 2 * δ)
    (hE : ∀ s ∈ Ioc t₀ t₁, cellRobot.M (x s) *ᵥ x'' s + cellRobot.C (x s) (x' s) *ᵥ x' s +
      cellRobot.N (x s) (x' s) = cellRobot.computedTorque ((ω ^ 2) • 1) ((2 * ω) • 1)
        (moveRef a b t₀ T) (moveRefDeriv a b t₀ T) (moveRefDeriv2 a b t₀ T) s (x s) (x' s) + d s)
    (h₀ : InTube ω δ (x t₀) (x' t₀) a 0) :
    (∀ t ∈ Icc t₀ t₁, InTube ω δ (x t) (x' t) (moveRef a b t₀ T t) (moveRefDeriv a b t₀ T t) ∧
      ∀ i, |x' t i - moveRefDeriv a b t₀ T t i| ≤ 2 * ω * δ) ∧
    ∀ t ∈ Icc (t₀ + T) t₁, InTube ω δ (x t) (x' t) b 0 ∧
      ∀ i, |x t i - b i| ≤ δ ∧ |x' t i| ≤ 2 * ω * δ := by
  refine move_tube_accel_right (Mt := fun s => cellRobot.M (x s))
    (Ct := fun s => cellRobot.C (x s) (x' s)) (Nt := fun s => cellRobot.N (x s) (x' s)) hω hT hc
    hx hx' (fun s hs w hMw i => ?_) hE h₀
  have h := Control.PosDef.inv_mulVec_mulVec (cellArm_M_posDef (x s)) w
  change (cellRobot.M (x s))⁻¹ *ᵥ (cellRobot.M (x s) *ᵥ w) = w at h
  rw [hMw] at h
  rw [← h]
  exact hacc s hs i

/-- **The loop's move corollary for the cell arm with the disturbance bounded at the
acceleration level and right derivatives (a design statement, not from MLS;
`cellArm_move_tube_accel_right`).** With `ω > 0`, a move duration `T > 0` and `(x, v)`
continuous on `[0, ∞)`, the arm's motion satisfies `Loop.MoveCorollary` for the quintic
reference and the tracking predicate `CellArmFollowsAccelRightAt`; no joint range and no inertia
constant enter. -/
theorem cellArm_moveCorollary_accel_right {W : Type*} (P : Loop.Params 3 W)
    (hT : 0 < P.duration) {ω δ : ℝ} (hω : 0 < ω) {x v acc d : ℝ → Fin 3 → ℝ}
    (hc : ContinuousOn (fun s => (x s, v s)) (Ici 0)) :
    Loop.MoveCorollary P (quinticMoveRef hT) δ ω
      (fun a b t₀ t =>
        CellArmFollowsAccelRightAt ω P.duration δ x v acc d (P.pos a) (P.pos b) t₀ t)
      x v := by
  intro a b _ t₀ t₁ ht₀ _ hf h₀ t ht
  exact ((cellArm_move_tube_accel_right hω hT (hc.mono fun s hs => ht₀.trans hs.1)
    (fun s hs => (hf s hs).1) (fun s hs => (hf s hs).2.1) (fun s hs => (hf s hs).2.2.1)
    (fun s hs => (hf s hs).2.2.2) h₀).1 t ht).1

end Cell
end RoboLean
