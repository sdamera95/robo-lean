import RoboLean.Dynamics.Lagrangian

/-!
# The pendulum on a wire and the double pendulum: Chapter 4 Exercise 1

MLS Chapter 4, Exercise 1, printed p. 208 (with its figures, read as a rendered image): "Derive the
equations of motion for the systems shown below. (a) Pendulum on a wire: an idealized planar
pendulum whose pivot is free to slide along a horizontal wire. Assume that the top of the pendulum
can move freely on the wire (no friction). (b) Double pendulum: two masses connected together by
massless links and revolute joints."

**Readings of the figures (recorded conventions).** (a) Coordinates `q = (x, θ)`: the pivot at
`(x, 0)` on the wire (the `x`-axis, `y` up), a point mass `m` on a massless rod of length `l`,
`θ` measured from the downward vertical, so the bob is at `(x + l sin θ, −l cos θ)`; the pivot is
massless. (b) Coordinates `q = (θ₁, θ₂)`: `θ₁` the angle of the first link from the downward
vertical, `θ₂` the angle of the second link relative to the first (the convention of the planar
two-link arm, Figure 4.4), point masses `m₁`, `m₂` at the ends of the massless links of lengths
`l₁`, `l₂`, weights `m₁ g`, `m₂ g` downward.

**Formalized.** For each system the kinetic energy computed from the velocity of each mass is
`½ q̇ᵀ M(q) q̇` (`wirePendulum_kineticEnergy`, `doublePendulum_kineticEnergy`), and Lagrange's
equations of the mechanical Lagrangian (4.20) with a generalized force `Υ` are the explicit
equations of motion (`wirePendulum_lagrangeEquationsAt_iff`, `doublePendulum_lagrangeEquationsAt_iff`):
(a) `m ẍ + m l cos θ θ̈ − m l sin θ θ̇² = Υ₁`, `m l cos θ ẍ + m l² θ̈ + m g l sin θ = Υ₂` (`Υ = 0`
for the free pendulum of the exercise); (b) the inertia and Coriolis terms of (4.11) with
`α = (m₁ + m₂) l₁² + m₂ l₂²`, `β = m₂ l₁ l₂`, `δ = m₂ l₂²`, plus the gravity term
`((m₁ + m₂) g l₁ sin θ₁ + m₂ g l₂ sin(θ₁ + θ₂), m₂ g l₂ sin(θ₁ + θ₂))`.

Lean index `0` is the book's first coordinate. Nothing here concerns a physical pendulum.
-/

noncomputable section
open Matrix Filter Topology

namespace RoboLean
namespace Examples

/-! ### (a) The pendulum on a wire -/

/-- **MLS Chapter 4, Exercise 1(a), p. 208: the inertia matrix of the pendulum on a wire,**
`M(x, θ) = [[m, m l cos θ], [m l cos θ, m l²]]` with `θ = q 1`. -/
def wirePendulumInertia (m l : ℝ) (q : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![m, m * l * Real.cos (q 1); m * l * Real.cos (q 1), m * l ^ 2]

/-- **MLS Chapter 4, Exercise 1(a), p. 208: the potential energy of the pendulum on a wire,**
`V = −m g l cos θ` (height of the bob `−l cos θ`). -/
def wirePendulumPotential (m g l : ℝ) (q : Fin 2 → ℝ) : ℝ :=
  -(m * g * l * Real.cos (q 1))

/-- **MLS Chapter 4, Exercise 1(a), p. 208: the kinetic energy from the bob's velocity.** The bob at
`(x + l sin θ, −l cos θ)` has velocity `(ẋ + l cos θ θ̇, l sin θ θ̇)`, and
`½ m |velocity|² = ½ q̇ᵀ M q̇`. -/
theorem wirePendulum_kineticEnergy (m l : ℝ) (q v : Fin 2 → ℝ) :
    (1 / 2 : ℝ) * m * ((v 0 + l * Real.cos (q 1) * v 1) ^ 2 + (l * Real.sin (q 1) * v 1) ^ 2) =
      (1 / 2 : ℝ) * (v ⬝ᵥ (wirePendulumInertia m l q *ᵥ v)) := by
  have h := Real.sin_sq_add_cos_sq (q 1)
  simp [wirePendulumInertia, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  linear_combination (1 / 2 : ℝ) * m * l ^ 2 * v 1 ^ 2 * h

private def wirePendulumInertiaDeriv (m l : ℝ) (q : Fin 2 → ℝ) :
    Fin 2 → Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
  ![![0, (-(m * l * Real.sin (q 1))) • (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ)],
    ![(-(m * l * Real.sin (q 1))) • (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ), 0]]

private theorem wirePendulumInertia_isSymm (m l : ℝ) (q : Fin 2 → ℝ) :
    (wirePendulumInertia m l q).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem hasFDerivAt_wirePendulumInertia (m l : ℝ) (q : Fin 2 → ℝ) (i j : Fin 2) :
    HasFDerivAt (fun p => wirePendulumInertia m l p i j) (wirePendulumInertiaDeriv m l q i j) q := by
  have hc := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 1 q
  fin_cases i <;> fin_cases j
  · exact hasFDerivAt_const (𝕜 := ℝ) m q
  · refine (hc.cos.const_mul (m * l)).congr_fderiv ?_
    ext v
    simp [wirePendulumInertiaDeriv]
    ring
  · refine (hc.cos.const_mul (m * l)).congr_fderiv ?_
    ext v
    simp [wirePendulumInertiaDeriv]
    ring
  · exact hasFDerivAt_const (𝕜 := ℝ) (m * l ^ 2) q

private theorem hasFDerivAt_wirePendulumPotential (m g l : ℝ) (q : Fin 2 → ℝ) :
    HasFDerivAt (wirePendulumPotential m g l)
      ((m * g * l * Real.sin (q 1)) • (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ)) q := by
  have hc := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 1 q
  refine (hc.cos.const_mul (m * g * l)).neg.congr_fderiv ?_
  ext v
  simp
  ring

/-- **MLS Chapter 4, Exercise 1(a), p. 208: the equations of motion of the pendulum on a wire.**
Along a trajectory `q = (x, θ)` whose velocity near `t` is `q'` and whose acceleration at `t` is
`q''`, Lagrange's equations of `½ q̇ᵀ M q̇ − V` with the generalized force `Υ` (`Υ = 0` for the free
pivot of the exercise) hold at `t` exactly when
`m ẍ + m l cos θ θ̈ − m l sin θ θ̇² = Υ₁` and `m l cos θ ẍ + m l² θ̈ + m g l sin θ = Υ₂`. -/
theorem wirePendulum_lagrangeEquationsAt_iff (m g l : ℝ) {q q' : ℝ → Fin 2 → ℝ} {q'' : Fin 2 → ℝ}
    {t : ℝ} (hq : ∀ᶠ s in 𝓝 t, HasDerivAt q (q' s) s) (hq' : HasDerivAt q' q'' t)
    (Υ : Fin 2 → ℝ) :
    Lagrangian.LagrangeEquationsAt
        (Lagrangian.mechanical (wirePendulumInertia m l) (wirePendulumPotential m g l)) q Υ t ↔
      m * q'' 0 + m * l * Real.cos (q t 1) * q'' 1 - m * l * Real.sin (q t 1) * q' t 1 ^ 2 = Υ 0 ∧
        m * l * Real.cos (q t 1) * q'' 0 + m * l ^ 2 * q'' 1 + m * g * l * Real.sin (q t 1) =
          Υ 1 := by
  rw [Lagrangian.lagrangeEquationsAt_mechanical_iff (wirePendulumInertia_isSymm m l)
    (hasFDerivAt_wirePendulumInertia m l (q t)) (hasFDerivAt_wirePendulumPotential m g l (q t))
    hq hq' Υ]
  have e : wirePendulumInertia m l (q t) *ᵥ q'' +
      Christoffel.coriolisMatrix (Christoffel.partials (wirePendulumInertiaDeriv m l (q t)))
        (q' t) *ᵥ q' t +
      Lagrangian.gradient
        ((m * g * l * Real.sin (q t 1)) • (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ)) =
      ![m * q'' 0 + m * l * Real.cos (q t 1) * q'' 1 - m * l * Real.sin (q t 1) * q' t 1 ^ 2,
        m * l * Real.cos (q t 1) * q'' 0 + m * l ^ 2 * q'' 1 + m * g * l * Real.sin (q t 1)] := by
    funext i
    simp only [Pi.add_apply, Christoffel.coriolisMatrix_mulVec]
    fin_cases i <;>
      simp [wirePendulumInertia, wirePendulumInertiaDeriv, Christoffel.symbol,
        Christoffel.partials, Lagrangian.gradient, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [e]
  constructor
  · intro h
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1

/-! ### (b) The double pendulum -/

/-- **MLS Chapter 4, Exercise 1(b), p. 208: the inertia matrix of the double pendulum,**
`[[α + 2β cos θ₂, δ + β cos θ₂], [δ + β cos θ₂, δ]]` with `α = (m₁ + m₂) l₁² + m₂ l₂²`,
`β = m₂ l₁ l₂`, `δ = m₂ l₂²` (the form of (4.10) for point masses at the link ends). -/
def doublePendulumInertia (m₁ m₂ l₁ l₂ : ℝ) (q : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(m₁ + m₂) * l₁ ^ 2 + m₂ * l₂ ^ 2 + 2 * (m₂ * l₁ * l₂) * Real.cos (q 1),
      m₂ * l₂ ^ 2 + m₂ * l₁ * l₂ * Real.cos (q 1);
    m₂ * l₂ ^ 2 + m₂ * l₁ * l₂ * Real.cos (q 1), m₂ * l₂ ^ 2]

/-- **MLS Chapter 4, Exercise 1(b), p. 208: the potential energy of the double pendulum,**
`V = −(m₁ + m₂) g l₁ cos θ₁ − m₂ g l₂ cos(θ₁ + θ₂)`. -/
def doublePendulumPotential (m₁ m₂ g l₁ l₂ : ℝ) (q : Fin 2 → ℝ) : ℝ :=
  -((m₁ + m₂) * g * l₁ * Real.cos (q 0)) - m₂ * g * l₂ * Real.cos (q 0 + q 1)

/-- **MLS Chapter 4, Exercise 1(b), p. 208: the kinetic energy from the velocities of the masses.**
The masses at `l₁ (sin θ₁, −cos θ₁)` and `l₁ (sin θ₁, −cos θ₁) + l₂ (sin(θ₁+θ₂), −cos(θ₁+θ₂))`
have velocities `l₁ θ̇₁ (cos θ₁, sin θ₁)` and that plus `l₂ (θ̇₁ + θ̇₂) (cos(θ₁+θ₂), sin(θ₁+θ₂))`,
and `½ m₁ |v₁|² + ½ m₂ |v₂|² = ½ q̇ᵀ M q̇`. -/
theorem doublePendulum_kineticEnergy (m₁ m₂ l₁ l₂ : ℝ) (q v : Fin 2 → ℝ) :
    (1 / 2 : ℝ) * m₁ * ((l₁ * Real.cos (q 0) * v 0) ^ 2 + (l₁ * Real.sin (q 0) * v 0) ^ 2) +
        (1 / 2 : ℝ) * m₂ *
          ((l₁ * Real.cos (q 0) * v 0 + l₂ * Real.cos (q 0 + q 1) * (v 0 + v 1)) ^ 2 +
            (l₁ * Real.sin (q 0) * v 0 + l₂ * Real.sin (q 0 + q 1) * (v 0 + v 1)) ^ 2) =
      (1 / 2 : ℝ) * (v ⬝ᵥ (doublePendulumInertia m₁ m₂ l₁ l₂ q *ᵥ v)) := by
  have h0 := Real.sin_sq_add_cos_sq (q 0)
  have h01 := Real.sin_sq_add_cos_sq (q 0 + q 1)
  have hc : Real.cos (q 1) = Real.cos (q 0 + q 1) * Real.cos (q 0) +
      Real.sin (q 0 + q 1) * Real.sin (q 0) := by
    rw [← Real.cos_sub]
    ring_nf
  simp [doublePendulumInertia, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  rw [hc]
  linear_combination (1 / 2 : ℝ) * m₁ * l₁ ^ 2 * v 0 ^ 2 * h0 +
    (1 / 2 : ℝ) * m₂ * l₁ ^ 2 * v 0 ^ 2 * h0 + (1 / 2 : ℝ) * m₂ * l₂ ^ 2 * (v 0 + v 1) ^ 2 * h01

private def doublePendulumInertiaDeriv (m₂ l₁ l₂ : ℝ) (q : Fin 2 → ℝ) :
    Fin 2 → Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
  ![![(-(2 * (m₂ * l₁ * l₂) * Real.sin (q 1))) •
        (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ),
      (-(m₂ * l₁ * l₂ * Real.sin (q 1))) • (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ)],
    ![(-(m₂ * l₁ * l₂ * Real.sin (q 1))) • (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ),
      0]]

private theorem doublePendulumInertia_isSymm (m₁ m₂ l₁ l₂ : ℝ) (q : Fin 2 → ℝ) :
    (doublePendulumInertia m₁ m₂ l₁ l₂ q).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem hasFDerivAt_doublePendulumInertia (m₁ m₂ l₁ l₂ : ℝ) (q : Fin 2 → ℝ)
    (i j : Fin 2) :
    HasFDerivAt (fun p => doublePendulumInertia m₁ m₂ l₁ l₂ p i j)
      (doublePendulumInertiaDeriv m₂ l₁ l₂ q i j) q := by
  have hc := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 1 q
  fin_cases i <;> fin_cases j
  · refine ((hc.cos.const_mul (2 * (m₂ * l₁ * l₂))).const_add
      ((m₁ + m₂) * l₁ ^ 2 + m₂ * l₂ ^ 2)).congr_fderiv ?_
    ext v
    simp [doublePendulumInertiaDeriv]
    ring
  · refine ((hc.cos.const_mul (m₂ * l₁ * l₂)).const_add (m₂ * l₂ ^ 2)).congr_fderiv ?_
    ext v
    simp [doublePendulumInertiaDeriv]
    ring
  · refine ((hc.cos.const_mul (m₂ * l₁ * l₂)).const_add (m₂ * l₂ ^ 2)).congr_fderiv ?_
    ext v
    simp [doublePendulumInertiaDeriv]
    ring
  · exact hasFDerivAt_const (𝕜 := ℝ) (m₂ * l₂ ^ 2) q

private theorem hasFDerivAt_doublePendulumPotential (m₁ m₂ g l₁ l₂ : ℝ) (q : Fin 2 → ℝ) :
    HasFDerivAt (doublePendulumPotential m₁ m₂ g l₁ l₂)
      (((m₁ + m₂) * g * l₁ * Real.sin (q 0) + m₂ * g * l₂ * Real.sin (q 0 + q 1)) •
          (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) +
        (m₂ * g * l₂ * Real.sin (q 0 + q 1)) •
          (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ)) q := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0 q
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 1 q
  refine ((h0.cos.const_mul ((m₁ + m₂) * g * l₁)).neg.sub
    ((h0.add h1).cos.const_mul (m₂ * g * l₂))).congr_fderiv ?_
  ext v
  simp
  ring

/-- **MLS Chapter 4, Exercise 1(b), p. 208: the equations of motion of the double pendulum.**
Along a trajectory `q = (θ₁, θ₂)` whose velocity near `t` is `q'` and whose acceleration at `t` is
`q''`, Lagrange's equations of `½ q̇ᵀ M q̇ − V` with the generalized force `Υ` (joint torques; `0` for
the free double pendulum) hold at `t` exactly when
`(α + 2β c₂) θ̈₁ + (δ + β c₂) θ̈₂ − β s₂ (2 θ̇₁ θ̇₂ + θ̇₂²) + (m₁ + m₂) g l₁ sin θ₁ + m₂ g l₂ sin(θ₁ + θ₂) = Υ₁`
and `(δ + β c₂) θ̈₁ + δ θ̈₂ + β s₂ θ̇₁² + m₂ g l₂ sin(θ₁ + θ₂) = Υ₂`, with
`α = (m₁ + m₂) l₁² + m₂ l₂²`, `β = m₂ l₁ l₂`, `δ = m₂ l₂²`, `c₂ = cos θ₂`, `s₂ = sin θ₂`. -/
theorem doublePendulum_lagrangeEquationsAt_iff (m₁ m₂ g l₁ l₂ : ℝ) {q q' : ℝ → Fin 2 → ℝ}
    {q'' : Fin 2 → ℝ} {t : ℝ} (hq : ∀ᶠ s in 𝓝 t, HasDerivAt q (q' s) s)
    (hq' : HasDerivAt q' q'' t) (Υ : Fin 2 → ℝ) :
    Lagrangian.LagrangeEquationsAt
        (Lagrangian.mechanical (doublePendulumInertia m₁ m₂ l₁ l₂)
          (doublePendulumPotential m₁ m₂ g l₁ l₂)) q Υ t ↔
      ((m₁ + m₂) * l₁ ^ 2 + m₂ * l₂ ^ 2 + 2 * (m₂ * l₁ * l₂) * Real.cos (q t 1)) * q'' 0 +
          (m₂ * l₂ ^ 2 + m₂ * l₁ * l₂ * Real.cos (q t 1)) * q'' 1 -
          m₂ * l₁ * l₂ * Real.sin (q t 1) * (2 * q' t 0 * q' t 1 + q' t 1 ^ 2) +
          (m₁ + m₂) * g * l₁ * Real.sin (q t 0) + m₂ * g * l₂ * Real.sin (q t 0 + q t 1) = Υ 0 ∧
        (m₂ * l₂ ^ 2 + m₂ * l₁ * l₂ * Real.cos (q t 1)) * q'' 0 + m₂ * l₂ ^ 2 * q'' 1 +
          m₂ * l₁ * l₂ * Real.sin (q t 1) * q' t 0 ^ 2 + m₂ * g * l₂ * Real.sin (q t 0 + q t 1) =
          Υ 1 := by
  rw [Lagrangian.lagrangeEquationsAt_mechanical_iff (doublePendulumInertia_isSymm m₁ m₂ l₁ l₂)
    (hasFDerivAt_doublePendulumInertia m₁ m₂ l₁ l₂ (q t))
    (hasFDerivAt_doublePendulumPotential m₁ m₂ g l₁ l₂ (q t)) hq hq' Υ]
  have e : doublePendulumInertia m₁ m₂ l₁ l₂ (q t) *ᵥ q'' +
      Christoffel.coriolisMatrix (Christoffel.partials (doublePendulumInertiaDeriv m₂ l₁ l₂ (q t)))
        (q' t) *ᵥ q' t +
      Lagrangian.gradient
        (((m₁ + m₂) * g * l₁ * Real.sin (q t 0) + m₂ * g * l₂ * Real.sin (q t 0 + q t 1)) •
            (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) +
          (m₂ * g * l₂ * Real.sin (q t 0 + q t 1)) •
            (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ)) =
      ![((m₁ + m₂) * l₁ ^ 2 + m₂ * l₂ ^ 2 + 2 * (m₂ * l₁ * l₂) * Real.cos (q t 1)) * q'' 0 +
          (m₂ * l₂ ^ 2 + m₂ * l₁ * l₂ * Real.cos (q t 1)) * q'' 1 -
          m₂ * l₁ * l₂ * Real.sin (q t 1) * (2 * q' t 0 * q' t 1 + q' t 1 ^ 2) +
          (m₁ + m₂) * g * l₁ * Real.sin (q t 0) + m₂ * g * l₂ * Real.sin (q t 0 + q t 1),
        (m₂ * l₂ ^ 2 + m₂ * l₁ * l₂ * Real.cos (q t 1)) * q'' 0 + m₂ * l₂ ^ 2 * q'' 1 +
          m₂ * l₁ * l₂ * Real.sin (q t 1) * q' t 0 ^ 2 + m₂ * g * l₂ * Real.sin (q t 0 + q t 1)] := by
    funext i
    simp only [Pi.add_apply, Christoffel.coriolisMatrix_mulVec]
    fin_cases i <;>
      simp [doublePendulumInertia, doublePendulumInertiaDeriv, Christoffel.symbol,
        Christoffel.partials, Lagrangian.gradient, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      ring
  rw [e]
  constructor
  · intro h
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1

end Examples
end RoboLean
