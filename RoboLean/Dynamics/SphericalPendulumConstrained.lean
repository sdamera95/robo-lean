import RoboLean.Dynamics.ConstrainedLagrangian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The spherical pendulum by the Lagrange–d'Alembert equations: Chapter 6 Exercise 1

MLS Chapter 6, Exercise 1, printed p. 314: "Calculate the dynamics of a spherical pendulum using the
Lagrange-d'Alembert equations and check that they agree with the result derived in Example 6.1."
Example 6.1 (p. 270) is the planar pendulum; the spherical pendulum is Example 4.1 (pp. 159–160),
whose equations (4.7) in the coordinates `(θ, φ)` are
`m l² θ̈ − m l² sin θ cos θ φ̇² + m g l sin θ = 0`, `m l² sin² θ φ̈ + 2 m l² sin θ cos θ θ̇ φ̇ = 0`.
The exercise is read with Example 4.1 (recorded source observation).

**Formalized.** A point mass `m` at `q ∈ ℝ³` with `L = ½ m |q̇|² − m g q₃` (`q₃` the height) and the
constraint `|q|² = l²` in Pfaffian form `A(q) = qᵀ` (`sphereConstraint`; `qᵀq̇ = 0` is half the
derivative of `|q|²`). Along the motion `q = l (sin θ cos φ, sin θ sin φ, −cos θ)` of Example 4.1's
coordinates (`sphericalPoint`), with `θ`, `φ` twice differentiable at `t`, the Lagrange–d'Alembert
equations with no applied force hold at `t` exactly when (4.7) holds at `t`, provided `l ≠ 0` and
`sin θ ≠ 0` (`sphericalPendulum_lagrangeDAlembertAt_iff`): the poles `sin θ = 0` are the singular
points of the coordinates, where the second equation of (4.7) is empty. The direction from the
Lagrange–d'Alembert equations to (4.7) needs neither hypothesis (`sphericalPendulum_of_lagrangeDAlembertAt`).

Conventions: Lean indices `0, 1, 2` for `x, y, z` with `z` up and gravity `−g` along `z`, so the
bob's height `−l cos θ` matches `V = −m g l cos θ` of Example 4.1. Nothing here concerns a physical
pendulum.
-/

noncomputable section
open Matrix Filter Topology

namespace RoboLean
namespace Examples

/-- **The constraint `|q|² = l²` in Pfaffian form (MLS Chapter 6, Exercise 1, p. 314, with p. 267):**
`A(q) = qᵀ`, so `A(q) q̇ = q · q̇ = ½ d/dt |q|²`. -/
def sphereConstraint (q : Fin 3 → ℝ) : Matrix (Fin 1) (Fin 3) ℝ :=
  Matrix.of fun _ j => q j

/-- **The inertia of a point mass in `ℝ³` (MLS Chapter 6, Exercise 1, p. 314):** `M = m I`. -/
def pointMassInertia (m : ℝ) (_q : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal fun _ => m

/-- **The gravitational potential of a point mass (MLS Chapter 6, Exercise 1, p. 314, with Example
4.1, p. 160):** `V(q) = m g q₃`, `q₃` the height. -/
def heightPotential (m g : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  m * g * q 2

/-- **The point of the sphere of radius `l` with the coordinates of MLS Example 4.1 (p. 159):**
`l (sin θ cos φ, sin θ sin φ, −cos θ)`, `θ` measured from the downward vertical. -/
def sphericalPoint (l θ φ : ℝ) : Fin 3 → ℝ :=
  ![l * Real.sin θ * Real.cos φ, l * Real.sin θ * Real.sin φ, -(l * Real.cos θ)]

private theorem frame_dot (a b : Fin 3 → ℝ) (θ φ : ℝ) :
    a ⬝ᵥ b =
      (a 0 * (Real.cos θ * Real.cos φ) + a 1 * (Real.cos θ * Real.sin φ) + a 2 * Real.sin θ) *
          (b 0 * (Real.cos θ * Real.cos φ) + b 1 * (Real.cos θ * Real.sin φ) + b 2 * Real.sin θ) +
        (-(a 0 * Real.sin φ) + a 1 * Real.cos φ) * (-(b 0 * Real.sin φ) + b 1 * Real.cos φ) +
        (a 0 * (Real.sin θ * Real.cos φ) + a 1 * (Real.sin θ * Real.sin φ) - a 2 * Real.cos θ) *
          (b 0 * (Real.sin θ * Real.cos φ) + b 1 * (Real.sin θ * Real.sin φ) -
            b 2 * Real.cos θ) := by
  have h1 := Real.sin_sq_add_cos_sq θ
  have h2 := Real.sin_sq_add_cos_sq φ
  simp only [dotProduct, Fin.sum_univ_three]
  linear_combination
    (-(a 0 * b 0 * Real.cos φ ^ 2 + a 1 * b 1 * Real.sin φ ^ 2 + a 2 * b 2 +
      (a 0 * b 1 + a 1 * b 0) * Real.cos φ * Real.sin φ)) * h1 - (a 0 * b 0 + a 1 * b 1) * h2

private theorem doesNoVirtualWork_sphere_iff {l θ φ : ℝ} (hl : l ≠ 0) (y : Fin 3 → ℝ) :
    Constrained.DoesNoVirtualWork (sphereConstraint (sphericalPoint l θ φ)) y ↔
      y 0 * (Real.cos θ * Real.cos φ) + y 1 * (Real.cos θ * Real.sin φ) + y 2 * Real.sin θ = 0 ∧
        -(y 0 * Real.sin φ) + y 1 * Real.cos φ = 0 := by
  have h1 := Real.sin_sq_add_cos_sq θ
  have h2 := Real.sin_sq_add_cos_sq φ
  have hA : ∀ δ : Fin 3 → ℝ, sphereConstraint (sphericalPoint l θ φ) *ᵥ δ = 0 ↔
      l * (δ 0 * (Real.sin θ * Real.cos φ) + δ 1 * (Real.sin θ * Real.sin φ) -
        δ 2 * Real.cos θ) = 0 := by
    intro δ
    constructor
    · intro h
      have := congrFun h 0
      simp [sphereConstraint, sphericalPoint, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
      linear_combination this
    · intro h
      funext i
      simp [sphereConstraint, sphericalPoint, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      linear_combination h
  constructor
  · intro hw
    have e1 := hw ![Real.cos θ * Real.cos φ, Real.cos θ * Real.sin φ, Real.sin θ]
      ((hA _).mpr (by simp; right; linear_combination Real.sin θ * Real.cos θ * h2))
    have e2 := hw ![-Real.sin φ, Real.cos φ, 0] ((hA _).mpr (by simp; right; ring))
    simp [dotProduct, Fin.sum_univ_three] at e1 e2
    exact ⟨by linear_combination e1, by linear_combination e2⟩
  · rintro ⟨e1, e2⟩ δ hδ
    have hn : δ 0 * (Real.sin θ * Real.cos φ) + δ 1 * (Real.sin θ * Real.sin φ) -
        δ 2 * Real.cos θ = 0 := by
      have := (hA δ).mp hδ
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hl
      · exact h
    rw [frame_dot y δ θ φ, e1, e2, hn]
    ring

private theorem hasDerivAt_sphericalPoint {l : ℝ} {θ φ θ' φ' : ℝ → ℝ} {s : ℝ}
    (hθ : HasDerivAt θ (θ' s) s) (hφ : HasDerivAt φ (φ' s) s) :
    HasDerivAt (fun r => sphericalPoint l (θ r) (φ r))
      ![l * (Real.cos (θ s) * Real.cos (φ s) * θ' s - Real.sin (θ s) * Real.sin (φ s) * φ' s),
        l * (Real.cos (θ s) * Real.sin (φ s) * θ' s + Real.sin (θ s) * Real.cos (φ s) * φ' s),
        l * (Real.sin (θ s) * θ' s)] s := by
  refine hasDerivAt_pi.mpr fun k => ?_
  fin_cases k
  · convert ((hθ.sin.const_mul l).mul hφ.cos) using 1
    · funext r
      simp [sphericalPoint]
    · simp
      ring
  · convert ((hθ.sin.const_mul l).mul hφ.sin) using 1
    · funext r
      simp [sphericalPoint]
    · simp
      ring
  · convert (hθ.cos.const_mul l).neg using 1
    · funext r
      simp [sphericalPoint]
    · simp

private theorem hasDerivAt_sphericalVelocity {l : ℝ} {θ φ θ' φ' : ℝ → ℝ} {θ'' φ'' t : ℝ}
    (hθ : HasDerivAt θ (θ' t) t) (hφ : HasDerivAt φ (φ' t) t) (hθ' : HasDerivAt θ' θ'' t)
    (hφ' : HasDerivAt φ' φ'' t) :
    HasDerivAt (fun s => ![l * (Real.cos (θ s) * Real.cos (φ s) * θ' s -
          Real.sin (θ s) * Real.sin (φ s) * φ' s),
        l * (Real.cos (θ s) * Real.sin (φ s) * θ' s + Real.sin (θ s) * Real.cos (φ s) * φ' s),
        l * (Real.sin (θ s) * θ' s)])
      ![l * (-(Real.sin (θ t) * Real.cos (φ t) * θ' t ^ 2) -
          2 * Real.cos (θ t) * Real.sin (φ t) * θ' t * φ' t + Real.cos (θ t) * Real.cos (φ t) * θ'' -
          Real.sin (θ t) * Real.cos (φ t) * φ' t ^ 2 - Real.sin (θ t) * Real.sin (φ t) * φ''),
        l * (-(Real.sin (θ t) * Real.sin (φ t) * θ' t ^ 2) +
          2 * Real.cos (θ t) * Real.cos (φ t) * θ' t * φ' t + Real.cos (θ t) * Real.sin (φ t) * θ'' -
          Real.sin (θ t) * Real.sin (φ t) * φ' t ^ 2 + Real.sin (θ t) * Real.cos (φ t) * φ''),
        l * (Real.cos (θ t) * θ' t ^ 2 + Real.sin (θ t) * θ'')] t := by
  refine hasDerivAt_pi.mpr fun k => ?_
  fin_cases k
  · convert ((((hθ.cos.mul hφ.cos).mul hθ').sub ((hθ.sin.mul hφ.sin).mul hφ')).const_mul l)
      using 1
    · funext r
      simp
    · simp
      left
      ring
  · convert ((((hθ.cos.mul hφ.sin).mul hθ').add ((hθ.sin.mul hφ.cos).mul hφ')).const_mul l)
      using 1
    · funext r
      simp
    · simp
      left
      ring
  · convert ((hθ.sin.mul hθ').const_mul l) using 1
    · funext r
      simp
    · simp
      left
      ring

private theorem reduction (m g l : ℝ) {θ φ θ' φ' : ℝ → ℝ} {θ'' φ'' t : ℝ}
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hφ : ∀ᶠ s in 𝓝 t, HasDerivAt φ (φ' s) s)
    (hθ' : HasDerivAt θ' θ'' t) (hφ' : HasDerivAt φ' φ'' t) :
    Constrained.LagrangeDAlembertAt (Lagrangian.mechanical (pointMassInertia m) (heightPotential m g))
        sphereConstraint (fun s => sphericalPoint l (θ s) (φ s)) 0 t ↔
      Constrained.DoesNoVirtualWork (sphereConstraint (sphericalPoint l (θ t) (φ t)))
        (m • ![l * (-(Real.sin (θ t) * Real.cos (φ t) * θ' t ^ 2) -
          2 * Real.cos (θ t) * Real.sin (φ t) * θ' t * φ' t + Real.cos (θ t) * Real.cos (φ t) * θ'' -
          Real.sin (θ t) * Real.cos (φ t) * φ' t ^ 2 - Real.sin (θ t) * Real.sin (φ t) * φ''),
        l * (-(Real.sin (θ t) * Real.sin (φ t) * θ' t ^ 2) +
          2 * Real.cos (θ t) * Real.cos (φ t) * θ' t * φ' t + Real.cos (θ t) * Real.sin (φ t) * θ'' -
          Real.sin (θ t) * Real.sin (φ t) * φ' t ^ 2 + Real.sin (θ t) * Real.cos (φ t) * φ''),
        l * (Real.cos (θ t) * θ' t ^ 2 + Real.sin (θ t) * θ'')] + ![0, 0, m * g]) := by
  have hM : ∀ i j, HasFDerivAt (fun q => pointMassInertia m q i j)
      (0 : (Fin 3 → ℝ) →L[ℝ] ℝ) (sphericalPoint l (θ t) (φ t)) := fun _ _ => hasFDerivAt_const _ _
  have hV : HasFDerivAt (heightPotential m g) ((m * g) • (ContinuousLinearMap.proj 2 :
      (Fin 3 → ℝ) →L[ℝ] ℝ)) (sphericalPoint l (θ t) (φ t)) := by
    have := (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 2
      (sphericalPoint l (θ t) (φ t))).const_mul (m * g)
    exact this
  have hsymm : ∀ q, (pointMassInertia m q).IsSymm := fun _ => Matrix.isSymm_diagonal _
  have hq : ∀ᶠ s in 𝓝 t, HasDerivAt (fun r => sphericalPoint l (θ r) (φ r))
      ![l * (Real.cos (θ s) * Real.cos (φ s) * θ' s - Real.sin (θ s) * Real.sin (φ s) * φ' s),
        l * (Real.cos (θ s) * Real.sin (φ s) * θ' s + Real.sin (θ s) * Real.cos (φ s) * φ' s),
        l * (Real.sin (θ s) * θ' s)] s := by
    filter_upwards [hθ, hφ] with s h1 h2
    exact hasDerivAt_sphericalPoint h1 h2
  rw [Constrained.lagrangeDAlembertAt_mechanical_iff (θ := fun s => sphericalPoint l (θ s) (φ s))
    (t := t) hsymm hM hV hq
    (hasDerivAt_sphericalVelocity hθ.self_of_nhds hφ.self_of_nhds hθ' hφ') 0]
  have hc : Christoffel.coriolisMatrix (Christoffel.partials fun _ _ =>
      (0 : (Fin 3 → ℝ) →L[ℝ] ℝ)) = fun _ => 0 := by
    funext v
    ext i j
    simp [Christoffel.coriolisMatrix, Christoffel.symbol, Christoffel.partials]
  have hg : Lagrangian.gradient ((m * g) • (ContinuousLinearMap.proj 2 :
      (Fin 3 → ℝ) →L[ℝ] ℝ)) = ![0, 0, m * g] := by
    funext i
    fin_cases i <;> simp [Lagrangian.gradient]
  have hMd : ∀ v : Fin 3 → ℝ, pointMassInertia m (sphericalPoint l (θ t) (φ t)) *ᵥ v = m • v := by
    intro v
    funext i
    simp [pointMassInertia, Matrix.mulVec_diagonal]
  rw [hc, hMd, hg, Matrix.zero_mulVec, add_zero, sub_zero]

/-- **The Lagrange–d'Alembert equations of the spherical pendulum give (4.7) (MLS Chapter 6,
Exercise 1, p. 314, with Example 4.1, eq. (4.7), p. 160).** Along `q = sphericalPoint l θ φ` with
`θ`, `φ` having the velocities `θ'`, `φ'` near `t` and the accelerations `θ''`, `φ''` at `t`: if the
Lagrange–d'Alembert equations for `L = ½ m |q̇|² − m g q₃`, `A(q) = qᵀ` and no applied force hold at
`t`, then (4.7) holds at `t`. -/
theorem sphericalPendulum_of_lagrangeDAlembertAt (m g l : ℝ) {θ φ θ' φ' : ℝ → ℝ} {θ'' φ'' t : ℝ}
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hφ : ∀ᶠ s in 𝓝 t, HasDerivAt φ (φ' s) s)
    (hθ' : HasDerivAt θ' θ'' t) (hφ' : HasDerivAt φ' φ'' t)
    (h : Constrained.LagrangeDAlembertAt (Lagrangian.mechanical (pointMassInertia m) (heightPotential m g))
      sphereConstraint (fun s => sphericalPoint l (θ s) (φ s)) 0 t) :
    m * l ^ 2 * θ'' - m * l ^ 2 * Real.sin (θ t) * Real.cos (θ t) * φ' t ^ 2 +
        m * g * l * Real.sin (θ t) = 0 ∧
      m * l ^ 2 * Real.sin (θ t) ^ 2 * φ'' +
        2 * m * l ^ 2 * Real.sin (θ t) * Real.cos (θ t) * θ' t * φ' t = 0 := by
  have h1 := Real.sin_sq_add_cos_sq (θ t)
  have h2 := Real.sin_sq_add_cos_sq (φ t)
  by_cases hl : l = 0
  · subst hl
    simp
  obtain ⟨e1, e2⟩ := (doesNoVirtualWork_sphere_iff hl _).mp
    ((reduction m g l hθ hφ hθ' hφ').mp h)
  simp at e1 e2
  constructor
  · linear_combination l * e1 - m * l ^ 2 * θ'' * h1 +
      (-(m * l ^ 2 * θ'' * Real.cos (θ t) ^ 2) +
        m * l ^ 2 * Real.sin (θ t) * Real.cos (θ t) * φ' t ^ 2 +
        m * l ^ 2 * Real.sin (θ t) * Real.cos (θ t) * θ' t ^ 2) * h2
  · linear_combination l * Real.sin (θ t) * e2 +
      (-(2 * m * l ^ 2 * Real.sin (θ t) * Real.cos (θ t) * θ' t * φ' t) -
        m * l ^ 2 * Real.sin (θ t) ^ 2 * φ'') * h2

/-- **MLS Chapter 6, Exercise 1, p. 314: the Lagrange–d'Alembert equations of the spherical
pendulum agree with (4.7) of Example 4.1 (p. 160).** Under the hypotheses of
`sphericalPendulum_of_lagrangeDAlembertAt`, with `l ≠ 0` and `sin θ(t) ≠ 0` (off the singular points
of the coordinates), the Lagrange–d'Alembert equations hold at `t` exactly when (4.7) holds at
`t`. -/
theorem sphericalPendulum_lagrangeDAlembertAt_iff (m g l : ℝ) {θ φ θ' φ' : ℝ → ℝ} {θ'' φ'' t : ℝ}
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hφ : ∀ᶠ s in 𝓝 t, HasDerivAt φ (φ' s) s)
    (hθ' : HasDerivAt θ' θ'' t) (hφ' : HasDerivAt φ' φ'' t) (hl : l ≠ 0)
    (hs : Real.sin (θ t) ≠ 0) :
    Constrained.LagrangeDAlembertAt (Lagrangian.mechanical (pointMassInertia m) (heightPotential m g))
        sphereConstraint (fun s => sphericalPoint l (θ s) (φ s)) 0 t ↔
      m * l ^ 2 * θ'' - m * l ^ 2 * Real.sin (θ t) * Real.cos (θ t) * φ' t ^ 2 +
          m * g * l * Real.sin (θ t) = 0 ∧
        m * l ^ 2 * Real.sin (θ t) ^ 2 * φ'' +
          2 * m * l ^ 2 * Real.sin (θ t) * Real.cos (θ t) * θ' t * φ' t = 0 := by
  refine ⟨sphericalPendulum_of_lagrangeDAlembertAt m g l hθ hφ hθ' hφ', ?_⟩
  rintro ⟨g1, g2⟩
  have h1 := Real.sin_sq_add_cos_sq (θ t)
  have h2 := Real.sin_sq_add_cos_sq (φ t)
  refine (reduction m g l hθ hφ hθ' hφ').mpr ((doesNoVirtualWork_sphere_iff hl _).mpr ⟨?_, ?_⟩)
  · refine (mul_eq_zero.mp ?_).resolve_left hl
    simp [-mul_eq_zero]
    linear_combination g1 + m * l ^ 2 * θ'' * h1 -
      (-(m * l ^ 2 * θ'' * Real.cos (θ t) ^ 2) +
        m * l ^ 2 * Real.sin (θ t) * Real.cos (θ t) * φ' t ^ 2 +
        m * l ^ 2 * Real.sin (θ t) * Real.cos (θ t) * θ' t ^ 2) * h2
  · refine (mul_eq_zero.mp ?_).resolve_left (mul_ne_zero hl hs)
    simp [-mul_eq_zero]
    linear_combination g2 -
      (-(2 * m * l ^ 2 * Real.sin (θ t) * Real.cos (θ t) * θ' t * φ' t) -
        m * l ^ 2 * Real.sin (θ t) ^ 2 * φ'') * h2

end Examples
end RoboLean
