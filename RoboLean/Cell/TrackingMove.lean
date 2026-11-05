import RoboLean.Cell.Tracking
import RoboLean.Cell.Reference

/-!
# The tracking tube along one move, and the handoff to the next move

A design statement, not from MLS. For a move from the waypoint `a` to the waypoint `b` admitted
at time `t₀` with duration `T > 0` (reference `moveRef a b t₀ T`), computed torque with the gains
`K_p = ω² I`, `K_v = 2ω I` (MLS eq. (4.49), p. 191, along a motion as on p. 301) under a
disturbance torque with `‖d‖₂ ≤ d̄ ≤ m₀ ω² δ` keeps the motion in the tube around the reference
on a finite horizon `[t₀, t₁]` when it starts in the tube around `a` at rest (`move_tube`). From
`t₀ + T` on, the reference is `b` at rest, so every joint is within `δ` of `b`, every joint speed
is at most `2 ω δ`, and the motion is in the tube around `b` at rest: the start condition of the
next move from `b` (the handoff). `move_tube_accel` is the same statement with the disturbance
bounded at the acceleration level (every `w` with `M(s) w = d(s)` has `|wᵢ| ≤ ω² δ`), without an
inertia bound.

Conventions as in `RoboLean.Cell.Tracking` and `RoboLean.Cell.Reference`: joint vectors
`Fin n → ℝ`, the Euclidean norm through `v ⬝ᵥ v`, per-joint tube bounds, time in seconds.
-/

noncomputable section

open Matrix Set

namespace RoboLean
namespace Cell

variable {n : ℕ}

/-- **The tube along one move and the handoff, with the disturbance bounded at the acceleration
level (a design statement, not from MLS; the law is MLS eq. (4.49), p. 191, along a motion as on
p. 301).** Let `ω > 0`, `T > 0`, and let the reference be `r = moveRef a b t₀ T` with velocity
`moveRefDeriv` and acceleration `moveRefDeriv2`. Let `(x, x')` be continuous on `[t₀, t₁]` and,
at every `s ∈ (t₀, t₁]`: `x` has velocity `x'` and `x'` has acceleration `x''`; every `w` with
`M(s) w = d(s)` satisfies `|wᵢ| ≤ ω² δ` (no inertia bound, no joint range); and
`M ẍ + C ẋ + N = F(s) + d(s)` with the computed torque `F` for the gains `ω² I`, `2ω I` and the
reference `r`. If at `t₀` the motion is in the tube around `a` at rest, then (1) at every
`t ∈ [t₀, t₁]` it is in the tube around `r(t)` with every joint speed within `2 ω δ` of the
reference speed; and (2) at every `t ∈ [t₀ + T, t₁]` it is in the tube around `b` at rest, every
joint is within `δ` of `b` and every joint speed is at most `2 ω δ`. -/
theorem move_tube_accel {ω δ t₀ t₁ T : ℝ} (hω : 0 < ω) (hT : 0 < T) {a b : Fin n → ℝ}
    {x x' x'' d : ℝ → Fin n → ℝ} {Mt Ct : ℝ → Matrix (Fin n) (Fin n) ℝ} {Nt : ℝ → Fin n → ℝ}
    (hc : ContinuousOn (fun s => (x s, x' s)) (Icc t₀ t₁))
    (hx : ∀ s ∈ Ioc t₀ t₁, HasDerivAt x (x' s) s) (hx' : ∀ s ∈ Ioc t₀ t₁, HasDerivAt x' (x'' s) s)
    (hw : ∀ s ∈ Ioc t₀ t₁, ∀ w, Mt s *ᵥ w = d s → ∀ i, |w i| ≤ ω ^ 2 * δ)
    (hE : ∀ s ∈ Ioc t₀ t₁, Mt s *ᵥ x'' s + Ct s *ᵥ x' s + Nt s =
      Control.computedTorqueAlong ((ω ^ 2) • 1) ((2 * ω) • 1) (Mt s) (Ct s) (Nt s)
        (moveRef a b t₀ T s) (moveRefDeriv a b t₀ T s) (moveRefDeriv2 a b t₀ T s) (x s) (x' s) +
        d s)
    (h₀ : InTube ω δ (x t₀) (x' t₀) a 0) :
    (∀ t ∈ Icc t₀ t₁, InTube ω δ (x t) (x' t) (moveRef a b t₀ T t) (moveRefDeriv a b t₀ T t) ∧
      ∀ i, |x' t i - moveRefDeriv a b t₀ T t i| ≤ 2 * ω * δ) ∧
    ∀ t ∈ Icc (t₀ + T) t₁, InTube ω δ (x t) (x' t) b 0 ∧
      ∀ i, |x t i - b i| ≤ δ ∧ |x' t i| ≤ 2 * ω * δ := by
  have h₀' : InTube ω δ (x t₀) (x' t₀) (moveRef a b t₀ T t₀) (moveRefDeriv a b t₀ T t₀) := by
    rwa [moveRef_of_le hT le_rfl, moveRefDeriv_of_le hT le_rfl]
  have htube := tube_invariant_on_accel hω (hasDerivAt_moveRef a b t₀ T)
    (hasDerivAt_moveRefDeriv a b t₀ T) hc hx hx' hw hE h₀'
  refine ⟨htube, fun t ht => ?_⟩
  have htI : t ∈ Icc t₀ t₁ := ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨h1, h2⟩ := htube t htI
  rw [moveRef_of_ge hT ht.1, moveRefDeriv_of_ge hT ht.1] at h1
  rw [moveRefDeriv_of_ge hT ht.1] at h2
  refine ⟨h1, fun i => ⟨h1.abs_sub_le i, ?_⟩⟩
  simpa using h2 i

/-- **The tube along one move and the handoff (a design statement, not from MLS; the law is MLS
eq. (4.49), p. 191, along a motion as on p. 301).** Let `ω > 0`, `m₀ > 0`, `δ < η`,
`0 ≤ d̄ ≤ m₀ ω² δ` and `T > 0`, and let the reference be `r = moveRef a b t₀ T` with velocity
`moveRefDeriv` and acceleration `moveRefDeriv2`. Let `(x, x')` be continuous on `[t₀, t₁]` and,
at every `s ∈ (t₀, t₁]`: `x` has velocity `x'` and `x'` has acceleration `x''`; if every joint
is within `η` of `r(s)` then `m₀ ‖v‖₂² ≤ vᵀ M(s) v` for every `v`; `‖d(s)‖₂ ≤ d̄`; and
`M ẍ + C ẋ + N = F(s) + d(s)` with the computed torque `F` for the gains `ω² I`, `2ω I` and the
reference `r`. If at `t₀` the motion is in the tube around `a` at rest, then
(1) at every `t ∈ [t₀, t₁]` it is in the tube around `r(t)` with every joint speed within
`2 ω δ` of the reference speed; and (2) at every `t ∈ [t₀ + T, t₁]` it is in the tube around `b`
at rest, every joint is within `δ` of `b` and every joint speed is at most `2 ω δ`. -/
theorem move_tube {ω δ η m₀ dbar t₀ t₁ T : ℝ} (hω : 0 < ω) (hm₀ : 0 < m₀) (hδη : δ < η)
    (hdbar₀ : 0 ≤ dbar) (hdbar : dbar ≤ m₀ * ω ^ 2 * δ) (hT : 0 < T) {a b : Fin n → ℝ}
    {x x' x'' d : ℝ → Fin n → ℝ} {Mt Ct : ℝ → Matrix (Fin n) (Fin n) ℝ} {Nt : ℝ → Fin n → ℝ}
    (hc : ContinuousOn (fun s => (x s, x' s)) (Icc t₀ t₁))
    (hx : ∀ s ∈ Ioc t₀ t₁, HasDerivAt x (x' s) s) (hx' : ∀ s ∈ Ioc t₀ t₁, HasDerivAt x' (x'' s) s)
    (hM : ∀ s ∈ Ioc t₀ t₁, (∀ i, |x s i - moveRef a b t₀ T s i| ≤ η) →
      ∀ v, m₀ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Mt s *ᵥ v))
    (hd : ∀ s ∈ Ioc t₀ t₁, d s ⬝ᵥ d s ≤ dbar ^ 2)
    (hE : ∀ s ∈ Ioc t₀ t₁, Mt s *ᵥ x'' s + Ct s *ᵥ x' s + Nt s =
      Control.computedTorqueAlong ((ω ^ 2) • 1) ((2 * ω) • 1) (Mt s) (Ct s) (Nt s)
        (moveRef a b t₀ T s) (moveRefDeriv a b t₀ T s) (moveRefDeriv2 a b t₀ T s) (x s) (x' s) +
        d s)
    (h₀ : InTube ω δ (x t₀) (x' t₀) a 0) :
    (∀ t ∈ Icc t₀ t₁, InTube ω δ (x t) (x' t) (moveRef a b t₀ T t) (moveRefDeriv a b t₀ T t) ∧
      ∀ i, |x' t i - moveRefDeriv a b t₀ T t i| ≤ 2 * ω * δ) ∧
    ∀ t ∈ Icc (t₀ + T) t₁, InTube ω δ (x t) (x' t) b 0 ∧
      ∀ i, |x t i - b i| ≤ δ ∧ |x' t i| ≤ 2 * ω * δ := by
  have h₀' : InTube ω δ (x t₀) (x' t₀) (moveRef a b t₀ T t₀) (moveRefDeriv a b t₀ T t₀) := by
    rwa [moveRef_of_le hT le_rfl, moveRefDeriv_of_le hT le_rfl]
  have htube := tube_invariant_on hω hm₀ hδη hdbar₀ hdbar (hasDerivAt_moveRef a b t₀ T)
    (hasDerivAt_moveRefDeriv a b t₀ T) hc hx hx' hM hd hE h₀'
  refine ⟨htube, fun t ht => ?_⟩
  have htI : t ∈ Icc t₀ t₁ := ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨h1, h2⟩ := htube t htI
  rw [moveRef_of_ge hT ht.1, moveRefDeriv_of_ge hT ht.1] at h1
  rw [moveRefDeriv_of_ge hT ht.1] at h2
  refine ⟨h1, fun i => ⟨h1.abs_sub_le i, ?_⟩⟩
  simpa using h2 i

end Cell
end RoboLean
