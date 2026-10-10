import RoboLean.Dynamics.Lagrangian

/-!
# Lagrange's equations of the spherical pendulum (MLS Example 4.1)

MLS Chapter 4, Example 4.1, printed pp. 159–160, Figure 4.1. A point mass `m` on a massless rod
of length `l` with generalized coordinates `q = (θ, φ)`, the angular displacements from the
`z`- and `x`-axes; Lean `q 0` is `θ` and `q 1` is `φ`. The book gives, on p. 160,

`T = ½ m l² (θ̇² + (1 − cos² θ) φ̇²)`, `V = −m g l cos θ`, `L = T − V`,

and the equations of motion (4.7) with zero generalized force:
`[[m l², 0], [0, m l² sin² θ]] (θ̈, φ̈) + (−m l² sin θ cos θ φ̇², 2 m l² sin θ cos θ θ̇ φ̇) +
(m g l sin θ, 0) = 0`.

Here the inertia matrix and the potential are entered as printed (the second diagonal entry as
`m l² (1 − cos² θ)`), and the general theorem `Lagrangian.lagrangeEquationsAt_mechanical_iff`,
with explicit Fréchet derivatives of the inertia entries and the potential, reproduces (4.7);
the Coriolis term is the Christoffel form (4.23) computed from those derivatives. This is one
instance (a convention check, not a general theorem), and nothing here concerns a physical
pendulum.
-/

noncomputable section
open Matrix Filter Topology

namespace RoboLean.Examples

/-- **The inertia matrix of the spherical pendulum, MLS Example 4.1, p. 160**, read from the
printed kinetic energy `T = ½ m l² (θ̇² + (1 − cos² θ) φ̇²)`:
`M(q) = [[m l², 0], [0, m l² (1 − cos² θ)]]` with `θ = q 0`. -/
def sphericalPendulumInertia (m l : ℝ) (q : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![m * l ^ 2, 0; 0, m * l ^ 2 * (1 - Real.cos (q 0) ^ 2)]

/-- **The potential energy of the spherical pendulum, MLS Example 4.1, p. 160**, as printed:
`V(q) = −m g l cos θ` with `θ = q 0` and `g` the gravitational constant. -/
def sphericalPendulumPotential (m g l : ℝ) (q : Fin 2 → ℝ) : ℝ :=
  -(m * g * l * Real.cos (q 0))

/-- **The Lagrangian of the spherical pendulum, MLS Example 4.1, p. 160**: the mechanical
Lagrangian `½ q̇ᵀ M(q) q̇ − V(q)` (eq. (4.20)) of `sphericalPendulumInertia` and
`sphericalPendulumPotential` is the printed
`L(q, q̇) = ½ m l² (θ̇² + (1 − cos² θ) φ̇²) + m g l cos θ`, with `q = (θ, φ) = (q 0, q 1)` and
`q̇ = v`. -/
theorem sphericalPendulum_lagrangian (m g l : ℝ) (q v : Fin 2 → ℝ) :
    Lagrangian.mechanical (sphericalPendulumInertia m l) (sphericalPendulumPotential m g l) q v =
      (1 / 2 : ℝ) * (m * l ^ 2) * (v 0 ^ 2 + (1 - Real.cos (q 0) ^ 2) * v 1 ^ 2) +
        m * g * l * Real.cos (q 0) := by
  simp [Lagrangian.mechanical, sphericalPendulumInertia, sphericalPendulumPotential,
    dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- Fréchet derivatives of the entries of `sphericalPendulumInertia` at `q`: only the second
diagonal entry varies, with derivative `m l² · 2 cos θ sin θ` along `θ = q 0`. -/
private def sphericalPendulumInertiaDeriv (m l : ℝ) (q : Fin 2 → ℝ) :
    Fin 2 → Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
  ![![0, 0], ![0, (m * l ^ 2 * (2 * Real.cos (q 0) * Real.sin (q 0))) •
    (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ)]]

private theorem sphericalPendulumInertia_isSymm (m l : ℝ) (q : Fin 2 → ℝ) :
    (sphericalPendulumInertia m l q).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem hasFDerivAt_sphericalPendulumInertia (m l : ℝ) (q : Fin 2 → ℝ) (i j : Fin 2) :
    HasFDerivAt (fun p => sphericalPendulumInertia m l p i j)
      (sphericalPendulumInertiaDeriv m l q i j) q := by
  have hc := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0 q
  fin_cases i <;> fin_cases j
  · exact hasFDerivAt_const (𝕜 := ℝ) (m * l ^ 2) q
  · exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) q
  · exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) q
  · refine (((hc.cos.pow 2).const_sub 1).const_mul (m * l ^ 2)).congr_fderiv ?_
    ext v
    simp [sphericalPendulumInertiaDeriv]
    ring

private theorem hasFDerivAt_sphericalPendulumPotential (m g l : ℝ) (q : Fin 2 → ℝ) :
    HasFDerivAt (sphericalPendulumPotential m g l)
      ((m * g * l * Real.sin (q 0)) • (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ)) q := by
  have hc := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0 q
  refine (hc.cos.const_mul (m * g * l)).neg.congr_fderiv ?_
  ext v
  simp
  ring

/-- **MLS Example 4.1, eq. (4.7), p. 160: the equations of motion of the spherical pendulum.**
Along a trajectory `θ` (Lean `θ s 0` is the book's `θ`, `θ s 1` is `φ`) whose velocity near `t`
is `θ'` and whose acceleration at `t` is `θ''`, Lagrange's equations (Theorem 4.1, p. 158) for
the printed Lagrangian with zero generalized force hold at `t` exactly when
`[[m l², 0], [0, m l² sin² θ]] θ̈ + (−m l² sin θ cos θ φ̇², 2 m l² sin θ cos θ θ̇ φ̇) +
(m g l sin θ, 0) = 0`, the printed (4.7). The printed `1 − cos² θ` becomes `sin² θ`. -/
theorem sphericalPendulum_lagrangeEquationsAt_iff (m g l : ℝ) {θ θ' : ℝ → Fin 2 → ℝ}
    {θ'' : Fin 2 → ℝ} {t : ℝ} (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s)
    (hθ' : HasDerivAt θ' θ'' t) :
    Lagrangian.LagrangeEquationsAt
        (Lagrangian.mechanical (sphericalPendulumInertia m l) (sphericalPendulumPotential m g l))
        θ 0 t ↔
      !![m * l ^ 2, 0; 0, m * l ^ 2 * Real.sin (θ t 0) ^ 2] *ᵥ θ'' +
        ![-(m * l ^ 2 * Real.sin (θ t 0) * Real.cos (θ t 0) * θ' t 1 ^ 2),
          2 * m * l ^ 2 * Real.sin (θ t 0) * Real.cos (θ t 0) * θ' t 0 * θ' t 1] +
        ![m * g * l * Real.sin (θ t 0), 0] = 0 := by
  rw [Lagrangian.lagrangeEquationsAt_mechanical_iff (sphericalPendulumInertia_isSymm m l)
    (hasFDerivAt_sphericalPendulumInertia m l (θ t))
    (hasFDerivAt_sphericalPendulumPotential m g l (θ t)) hθ hθ' 0]
  have hsc := Real.sin_sq_add_cos_sq (θ t 0)
  have e : sphericalPendulumInertia m l (θ t) *ᵥ θ'' +
      Christoffel.coriolisMatrix (Christoffel.partials (sphericalPendulumInertiaDeriv m l (θ t)))
        (θ' t) *ᵥ θ' t +
      Lagrangian.gradient
        ((m * g * l * Real.sin (θ t 0)) • (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ)) =
      !![m * l ^ 2, 0; 0, m * l ^ 2 * Real.sin (θ t 0) ^ 2] *ᵥ θ'' +
        ![-(m * l ^ 2 * Real.sin (θ t 0) * Real.cos (θ t 0) * θ' t 1 ^ 2),
          2 * m * l ^ 2 * Real.sin (θ t 0) * Real.cos (θ t 0) * θ' t 0 * θ' t 1] +
        ![m * g * l * Real.sin (θ t 0), 0] := by
    funext i
    simp only [Pi.add_apply, Christoffel.coriolisMatrix_mulVec]
    fin_cases i <;>
      simp [sphericalPendulumInertia, sphericalPendulumInertiaDeriv, Christoffel.symbol,
        Christoffel.partials, Lagrangian.gradient, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · ring
    · linear_combination (-(m * l ^ 2 * θ'' 1)) * hsc
  rw [e]

end RoboLean.Examples
