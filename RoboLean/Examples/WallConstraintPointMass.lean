import RoboLean.Examples.WallConstraint
import RoboLean.Examples.PlanarTwoLinkDynamics
import RoboLean.Dynamics.ConstrainedLagrangian

/-!
# The wall of Chapter 6, Exercise 7(b): joint-space dynamics with point masses

MLS Chapter 6, Exercise 7, printed p. 315: "(b) Calculate the dynamics of the manipulator assuming
that the end-effector remains in contact with the wall at `x = c`. Model the inertia of each link as
a point mass concentrated at the middle of the link."

Model. The planar two-link arm of MLS Figure 4.4 (p. 164; `Examples.planarTwoLinkArm`, angles from
`+x`, the arm of the wall figure) with link masses `m₁, m₂` at the link midpoints, `r₁ = l₁/2`,
`r₂ = l₂/2`, and zero rotational inertia (`I₁ = I₂ = 0`): the inertia matrix (4.10) becomes
`M(θ) = [[m₁l₁²/4 + m₂(l₁² + l₂²/4) + m₂l₁l₂ cos θ₂, m₂l₂²/4 + ½m₂l₁l₂ cos θ₂],
[m₂l₂²/4 + ½m₂l₁l₂ cos θ₂, m₂l₂²/4]]` and the Coriolis matrix (4.12) has `β = ½m₂l₁l₂`. No
potential is included: the exercise names no gravity and the arm of §6.3 moves in a horizontal
plane (a reading). The wall constraint is `h(θ) = l₁ cos θ₁ + l₂ cos(θ₁ + θ₂) − c = 0` with
gradient row `A(θ) = ∇h(θ)` (part (a), `jac_wallJointConstraint`). The dynamics are the
multiplier form (6.4)–(6.5) of p. 269, `M(θ)θ̈ + C(θ, θ̇)θ̇ + A(θ)ᵀλ = τ`, with the book's sign of
the multiplier term.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean.Examples

/-- The inertia matrix of the planar two-link arm with point masses `m₁`, `m₂` at the link midpoints
(MLS Exercise 7(b), p. 315, from eq. (4.10), p. 165, with `r₁ = l₁/2`, `r₂ = l₂/2`, `I_z1 = I_z2 = 0`):
`[[m₁l₁²/4 + m₂(l₁² + l₂²/4) + m₂l₁l₂ cos θ₂, m₂l₂²/4 + ½m₂l₁l₂ cos θ₂], [·, m₂l₂²/4]]`. -/
def wallPointMassInertia (m₁ m₂ l₁ l₂ : ℝ) (θ : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![m₁ * l₁ ^ 2 / 4 + m₂ * (l₁ ^ 2 + l₂ ^ 2 / 4) + m₂ * l₁ * l₂ * Real.cos (θ 1),
      m₂ * l₂ ^ 2 / 4 + m₂ * l₁ * l₂ / 2 * Real.cos (θ 1);
    m₂ * l₂ ^ 2 / 4 + m₂ * l₁ * l₂ / 2 * Real.cos (θ 1), m₂ * l₂ ^ 2 / 4]

/-- The Coriolis matrix of the point-mass arm (MLS Exercise 7(b), p. 315, from eq. (4.12),
p. 167, with `β = ½ m₂ l₁ l₂`): `[[−β sin θ₂ θ̇₂, −β sin θ₂ (θ̇₁ + θ̇₂)], [β sin θ₂ θ̇₁, 0]]`. -/
def wallPointMassCoriolis (m₂ l₁ l₂ : ℝ) (θ θ' : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(m₂ * l₁ * l₂ / 2) * Real.sin (θ 1) * θ' 1,
      -(m₂ * l₁ * l₂ / 2) * Real.sin (θ 1) * (θ' 0 + θ' 1);
    m₂ * l₁ * l₂ / 2 * Real.sin (θ 1) * θ' 0, 0]

/-- The gradient row `A(θ) = ∇h(θ) = [−l₁ sin θ₁ − l₂ sin(θ₁ + θ₂), −l₂ sin(θ₁ + θ₂)]` of the wall
constraint `h(θ) = l₁ cos θ₁ + l₂ cos(θ₁ + θ₂) − c` (MLS Exercise 7(a), p. 315; the slot of p. 204
with `α = π/2`). -/
def wallGradient (l₁ l₂ : ℝ) (θ : Fin 2 → ℝ) : Matrix (Fin 1) (Fin 2) ℝ :=
  !![-(l₁ * Real.sin (θ 0)) - l₂ * Real.sin (θ 0 + θ 1), -(l₂ * Real.sin (θ 0 + θ 1))]

/-- The gradient row is the Jacobian of the wall constraint in joint coordinates (MLS
Exercise 7(a), p. 315). -/
theorem wallGradient_eq_jac (l₁ l₂ c : ℝ) (θ : Fin 2 → ℝ) :
    wallGradient l₁ l₂ θ = MapJacobian.jac (fun q => wallConstraint c (planarArmXY l₁ l₂ q)) θ := by
  rw [jac_wallJointConstraint]
  rfl

/-- **MLS Exercise 7(b), p. 315: the inertia matrix with point masses at the link midpoints.** The
inertia matrix of eq. (4.10) of the arm of Figure 4.4 with `r₁ = l₁/2`, `r₂ = l₂/2` and zero
rotational inertia is `wallPointMassInertia`. -/
theorem planarTwoLinkArm_pointMass_massMatrix (m₁ m₂ l₁ l₂ : ℝ) (θ : Fin 2 → ℝ) :
    (planarTwoLinkArm m₁ m₂ (l₁ / 2) (l₂ / 2) l₁ 0 0).massMatrix θ =
      wallPointMassInertia m₁ m₂ l₁ l₂ θ := by
  rw [planarTwoLinkArm_massMatrix, wallPointMassInertia]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

/-- **MLS Exercise 7(b), p. 315: the Coriolis matrix with point masses at the link midpoints.** The
Coriolis matrix (4.23) built from the derivatives of the point-mass inertia matrix is
`wallPointMassCoriolis`. -/
theorem planarTwoLinkArm_pointMass_coriolisMatrix (m₂ l₁ l₂ : ℝ) (θ θ' : Fin 2 → ℝ) :
    Christoffel.coriolisMatrix
        (Christoffel.partials (planarTwoLinkArmMassDeriv m₂ (l₂ / 2) l₁ θ)) θ' =
      wallPointMassCoriolis m₂ l₁ l₂ θ θ' := by
  rw [planarTwoLinkArm_coriolisMatrix, wallPointMassCoriolis]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

/-- **MLS Exercise 7(b), p. 315, with eqs. (6.4)–(6.5), p. 269: the dynamics of the arm on the wall
`x = c` with point masses at the link midpoints.** Along a motion `θ` with velocity `θ'` near `t` and
acceleration `θ''` at `t`, Lagrange's equations with the constraint force `A(θ)ᵀλ` for the Lagrangian
`½ θ̇ᵀM(θ)θ̇` of the point-mass arm hold at `t` exactly when
`M(θ)θ̈ + C(θ, θ̇)θ̇ + ∇h(θ)ᵀλ = τ` with the explicit point-mass `M` and `C`. -/
theorem wall_pointMass_multiplierEquationsAt_iff (m₁ m₂ l₁ l₂ : ℝ) {θ θ' : ℝ → Fin 2 → ℝ}
    {θ'' : Fin 2 → ℝ} {t : ℝ} (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s)
    (hθ' : HasDerivAt θ' θ'' t) (τ : Fin 2 → ℝ) (μ : Fin 1 → ℝ) :
    Constrained.MultiplierEquationsAt
        (Lagrangian.mechanical (planarTwoLinkArm m₁ m₂ (l₁ / 2) (l₂ / 2) l₁ 0 0).massMatrix
          (fun _ => 0))
        (wallGradient l₁ l₂) θ τ μ t ↔
      wallPointMassInertia m₁ m₂ l₁ l₂ (θ t) *ᵥ θ'' +
          wallPointMassCoriolis m₂ l₁ l₂ (θ t) (θ' t) *ᵥ θ' t +
          (wallGradient l₁ l₂ (θ t))ᵀ *ᵥ μ = τ := by
  have hsymm : ∀ q, ((planarTwoLinkArm m₁ m₂ (l₁ / 2) (l₂ / 2) l₁ 0 0).massMatrix q).IsSymm := by
    intro q
    rw [planarTwoLinkArm_pointMass_massMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [wallPointMassInertia]
  rw [Constrained.multiplierEquationsAt_mechanical_iff hsymm
    (hasFDerivAt_planarTwoLinkArm_massMatrix m₁ m₂ (l₁ / 2) (l₂ / 2) l₁ 0 0 (θ t))
    (hasFDerivAt_const 0 (θ t)) hθ hθ', planarTwoLinkArm_pointMass_massMatrix,
    planarTwoLinkArm_pointMass_coriolisMatrix]
  have hg : Lagrangian.gradient (0 : (Fin 2 → ℝ) →L[ℝ] ℝ) = 0 := by
    funext i
    simp [Lagrangian.gradient]
  rw [hg, add_zero]

/-- The potential energy of the point masses under gravity `g` along `−y` in the plane of the arm
(MLS Exercise 7(b), p. 315, with the potential of MLS p. 169): `V(θ) = g(m₁(l₁/2) sin θ₁ +
m₂(l₁ sin θ₁ + (l₂/2) sin(θ₁ + θ₂)))`, the heights of the link midpoints. -/
def wallPointMassPotential (m₁ m₂ l₁ l₂ g : ℝ) (θ : Fin 2 → ℝ) : ℝ :=
  g * (m₁ * (l₁ / 2) * Real.sin (θ 0) + m₂ * (l₁ * Real.sin (θ 0) + l₂ / 2 * Real.sin (θ 0 + θ 1)))

/-- The gravity term `N(θ) = ∂V/∂θ` of the point masses (MLS Exercise 7(b), p. 315, with
eq. (4.23)'s `∂V/∂θ`): `(g((m₁/2 + m₂)l₁ cos θ₁ + (m₂l₂/2) cos(θ₁ + θ₂)), g(m₂l₂/2) cos(θ₁ + θ₂))`. -/
def wallPointMassGravityTerm (m₁ m₂ l₁ l₂ g : ℝ) (θ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![g * ((m₁ / 2 + m₂) * l₁ * Real.cos (θ 0) + m₂ * l₂ / 2 * Real.cos (θ 0 + θ 1)),
    g * (m₂ * l₂ / 2 * Real.cos (θ 0 + θ 1))]

/-- **MLS Exercise 7(b), p. 315, with gravity: the dynamics of the arm on the wall `x = c` with
point masses at the link midpoints and gravity `g` along `−y`.** Along a motion with velocity `θ'`
near `t` and acceleration `θ''` at `t`, Lagrange's equations with the constraint force `A(θ)ᵀλ` for
`½ θ̇ᵀM(θ)θ̇ − V(θ)` hold at `t` exactly when `M(θ)θ̈ + C(θ, θ̇)θ̇ + N(θ) + ∇h(θ)ᵀλ = τ` with the
explicit point-mass `M`, `C` and gravity term `N`. -/
theorem wall_pointMass_gravity_multiplierEquationsAt_iff (m₁ m₂ l₁ l₂ g : ℝ)
    {θ θ' : ℝ → Fin 2 → ℝ} {θ'' : Fin 2 → ℝ} {t : ℝ} (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s)
    (hθ' : HasDerivAt θ' θ'' t) (τ : Fin 2 → ℝ) (μ : Fin 1 → ℝ) :
    Constrained.MultiplierEquationsAt
        (Lagrangian.mechanical (planarTwoLinkArm m₁ m₂ (l₁ / 2) (l₂ / 2) l₁ 0 0).massMatrix
          (wallPointMassPotential m₁ m₂ l₁ l₂ g))
        (wallGradient l₁ l₂) θ τ μ t ↔
      wallPointMassInertia m₁ m₂ l₁ l₂ (θ t) *ᵥ θ'' +
          wallPointMassCoriolis m₂ l₁ l₂ (θ t) (θ' t) *ᵥ θ' t +
          wallPointMassGravityTerm m₁ m₂ l₁ l₂ g (θ t) +
          (wallGradient l₁ l₂ (θ t))ᵀ *ᵥ μ = τ := by
  have hsymm : ∀ q, ((planarTwoLinkArm m₁ m₂ (l₁ / 2) (l₂ / 2) l₁ 0 0).massMatrix q).IsSymm := by
    intro q
    rw [planarTwoLinkArm_pointMass_massMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [wallPointMassInertia]
  have p0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0 (θ t)
  have p1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 1 (θ t)
  have hV := ((p0.sin.const_mul (m₁ * (l₁ / 2))).add
    (((p0.sin.const_mul l₁).add ((p0.add p1).sin.const_mul (l₂ / 2))).const_mul m₂)).const_mul g
  have hV' : HasFDerivAt (wallPointMassPotential m₁ m₂ l₁ l₂ g)
      (_ : (Fin 2 → ℝ) →L[ℝ] ℝ) (θ t) := hV
  rw [Constrained.multiplierEquationsAt_mechanical_iff hsymm
    (hasFDerivAt_planarTwoLinkArm_massMatrix m₁ m₂ (l₁ / 2) (l₂ / 2) l₁ 0 0 (θ t))
    hV' hθ hθ', planarTwoLinkArm_pointMass_massMatrix,
    planarTwoLinkArm_pointMass_coriolisMatrix]
  rw [show Lagrangian.gradient _ = wallPointMassGravityTerm m₁ m₂ l₁ l₂ g (θ t) from ?_]
  funext i
  fin_cases i <;>
    simp [Lagrangian.gradient, wallPointMassGravityTerm, Pi.add_apply, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff] <;> ring

end RoboLean.Examples
