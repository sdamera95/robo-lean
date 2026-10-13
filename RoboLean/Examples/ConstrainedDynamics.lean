import RoboLean.Dynamics.ConstrainedLagrangian

/-!
# Examples 6.1 and 6.2 of MLS: the idealized planar pendulum and the rolling disk

MLS Chapter 6, §1, printed pp. 270–274 (renders inspected this session).

**Example 6.1 (pp. 270–271), the idealized planar pendulum.** Configuration `q = (x, y) ∈ ℝ²`,
holonomic constraint `x² + y² = l²`, Pfaffian constraint `A(q) = [x y]` ("Differentiating this
constraint and dividing by two"), Lagrangian `L = ½ m (ẋ² + ẏ²) − m g y`, no applied force. The
equations of motion (6.5) are `m q̈ + (0, m g) + (x, y) λ = 0`, and (6.6) gives
`λ = (m / (x² + y²)) (ẋ² + ẏ² − g y) = (m / l²)(ẋ² + ẏ² − g y)` on the circle
(`pendulum_multiplierEquationsAt_iff`). MLS prints `λ = −(m / l²)(g y + ẋ² + ẏ²)`, from a version of
(6.6) with `− Ȧ q̇` in place of the `+ Ȧ q̇` of (6.6) on p. 270, and the tension
`(m g / l) y + (m / l)(ẋ² + ẏ²)`; both differ from the values computed here (E034 source
observation, one-input evaluation in the gate's `Observation.lean`). The tension `‖(x, y) λ‖` is
computed with the Euclidean norm, written out (`pendulum_tension`).

**Example 6.2 (pp. 272–274), the rolling disk.** Configuration `q = (x, y, θ, φ)` (Lean indices
`0, 1, 2, 3`), rolling constraint (6.10) `A(q) = [[1, 0, 0, −ρ cos θ], [0, 1, 0, −ρ sin θ]]`,
Lagrangian `L = ½ m (ẋ² + ẏ²) + ½ I₁ θ̇² + ½ I₂ φ̇²`, generalized force `(0, 0, τ_θ, τ_φ)`. Proved:
the rows of (6.10) are everywhere independent; the virtual displacements (6.11); the
Lagrange–d'Alembert equations are (6.12); the differentiated constraints (6.13); and along a motion
satisfying the constraint near `t`, (6.12) is (6.14), `diag(I₁, I₂ + m ρ²) (θ̈, φ̈) = (τ_θ, τ_φ)`.
MLS describes `I₁` as the inertia "about the horizontal (rolling) axis" and `I₂` "about the vertical
axis" and calls `τ_θ` the driving and `τ_φ` the steering torque, while `θ` is the heading and `φ`
the rolling angle; the formulas use only the symbols, so these labels do not enter the statements
(E034 source observation).

Nothing here concerns a physical pendulum or disk, friction, or existence of motions.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Examples

/-! ### Example 6.1: the idealized planar pendulum (MLS pp. 270–271) -/

/-- **MLS Example 6.1, p. 270: the Pfaffian constraint `A(q) = [x y]`** of the planar pendulum,
`q = (x, y)` (Lean indices `0, 1`). -/
def pendulumConstraint (q : Fin 2 → ℝ) : Matrix (Fin 1) (Fin 2) ℝ :=
  Matrix.of fun _ j => q j

/-- **MLS Example 6.1, p. 270: the holonomic constraint `x² + y² = l²`,** as `h(q) = x² + y² − l²`.
-/
def pendulumHolonomic (l : ℝ) (q : Fin 2 → ℝ) : Fin 1 → ℝ :=
  fun _ => q 0 ^ 2 + q 1 ^ 2 - l ^ 2

/-- **MLS Example 6.1, p. 270: the inertia `m I` of the point mass.** -/
def pendulumInertia (m : ℝ) (_q : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  m • (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- **MLS Example 6.1, p. 270: the potential energy `m g y`.** -/
def pendulumPotential (m g : ℝ) (q : Fin 2 → ℝ) : ℝ :=
  m * g * q 1

/-- **MLS Example 6.1, p. 270: the unconstrained Lagrangian** `L = ½ q̇ᵀ (m I) q̇ − m g y` as a
mechanical Lagrangian (MLS eq. (4.20)). -/
def pendulumLagrangian (m g : ℝ) : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ :=
  Lagrangian.mechanical (pendulumInertia m) (pendulumPotential m g)

/-- **MLS Example 6.1, p. 270: "The (unconstrained) Lagrangian is simply
`L(q, q̇) = ½ m (ẋ² + ẏ²) − m g y`."** -/
theorem pendulumLagrangian_apply (m g : ℝ) (q v : Fin 2 → ℝ) :
    pendulumLagrangian m g q v = 1 / 2 * m * (v 0 ^ 2 + v 1 ^ 2) - m * g * q 1 := by
  simp only [pendulumLagrangian, Lagrangian.mechanical, pendulumInertia, pendulumPotential,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- **MLS Example 6.1, p. 270: "Differentiating this constraint and dividing by two, we obtain the
Pfaffian constraint `[x y] q̇ = 0`":** `∂h/∂q = 2 [x y]`. -/
theorem jac_pendulumHolonomic (l : ℝ) (q : Fin 2 → ℝ) :
    MapJacobian.jac (pendulumHolonomic l) q = (2 : ℝ) • pendulumConstraint q := by
  have h : ∀ i : Fin 1, HasFDerivAt (fun x => pendulumHolonomic l x i)
      ((2 * q 0) • ContinuousLinearMap.proj 0 + (2 * q 1) • ContinuousLinearMap.proj 1 :
        (Fin 2 → ℝ) →L[ℝ] ℝ) q := by
    intro i
    have h0 := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) q).pow 2
    have h1 := (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) q).pow 2
    refine ((h0.add h1).sub_const (l ^ 2)).congr_fderiv ?_
    ext v
    simp [nsmul_eq_mul]
  ext i j
  rw [MapJacobian.jac_apply_of_hasFDerivAt h]
  fin_cases i; fin_cases j <;> simp [pendulumConstraint]

/-- **MLS Example 6.1, p. 270: a motion on the circle `x² + y² = l²` near `t` satisfies the Pfaffian
constraint `x ẋ + y ẏ = 0` near `t`.** -/
theorem pendulum_eventually_pfaffianAt {l : ℝ} {θ θ' : ℝ → Fin 2 → ℝ} {t : ℝ}
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s)
    (hc : ∀ᶠ s in 𝓝 t, θ s 0 ^ 2 + θ s 1 ^ 2 = l ^ 2) :
    ∀ᶠ s in 𝓝 t, Constrained.PfaffianAt pendulumConstraint (θ s) (θ' s) := by
  have hh : Differentiable ℝ (pendulumHolonomic l) := by
    unfold pendulumHolonomic
    fun_prop
  have hc' : ∀ᶠ s in 𝓝 t, pendulumHolonomic l (θ s) = 0 := by
    filter_upwards [hc] with s hs
    funext _
    simp [pendulumHolonomic, hs]
  filter_upwards [Constrained.eventually_pfaffianAt_jac hh hθ hc'] with s hs
  rw [Constrained.PfaffianAt, jac_pendulumHolonomic, Matrix.smul_mulVec] at hs
  exact (smul_eq_zero.mp hs).resolve_left two_ne_zero

/-- **MLS Example 6.1 (p. 267's independence assumption):** the constraint `[x y]` has independent
rows at every configuration other than the origin. -/
theorem pendulumConstraint_linearIndependent {q : Fin 2 → ℝ} (hq : q ≠ 0) :
    LinearIndependent ℝ (pendulumConstraint q).row := by
  rw [linearIndependent_unique_iff]
  exact hq

/-- The Coriolis matrix of a configuration-independent inertia (all partial derivatives zero)
vanishes (MLS eq. (4.23)). -/
private theorem coriolisMatrix_partials_zero {n : ℕ} (v : Fin n → ℝ) :
    Christoffel.coriolisMatrix
        (Christoffel.partials fun _ _ => (0 : (Fin n → ℝ) →L[ℝ] ℝ)) v = 0 := by
  ext i j
  simp [Christoffel.coriolisMatrix, Christoffel.symbol, Christoffel.partials]

/-- The left side of (6.5) for the pendulum, `m q̈ + C q̇ + ∂V/∂q + Aᵀ λ` with `C = 0` and
`∂V/∂q = (0, m g)` (MLS Example 6.1, p. 270). -/
private theorem pendulum_lhs (m g : ℝ) (x v a : Fin 2 → ℝ) (μ : Fin 1 → ℝ) :
    pendulumInertia m x *ᵥ a +
        Christoffel.coriolisMatrix
          (Christoffel.partials fun _ _ => (0 : (Fin 2 → ℝ) →L[ℝ] ℝ)) v *ᵥ v +
        Lagrangian.gradient
          ((m * g) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) +
        (pendulumConstraint x)ᵀ *ᵥ μ =
      m • a + ![0, m * g] + μ 0 • x := by
  rw [coriolisMatrix_partials_zero, Matrix.zero_mulVec, add_zero]
  funext i
  fin_cases i <;>
    simp [pendulumInertia, pendulumConstraint, Lagrangian.gradient, Matrix.mulVec, dotProduct,
      mul_comm, Matrix.vecHead, Matrix.vecTail]

/-- **The multiplier (6.6) of the pendulum (MLS Example 6.1, p. 270)** with the force
`w = (0, −m g)` and `Ȧ q̇ = [ẋ ẏ] q̇`: `λ = (m / (x² + y²))(ẋ² + ẏ² − g y)`. Computed through
`Constrained.add_eq_zero_iff_eq_multiplier` with the acceleration `(w − Aᵀ λ) / m`. -/
private theorem pendulum_multiplier {m : ℝ} (hm : 0 < m) (g : ℝ) {x : Fin 2 → ℝ} (hx : x ≠ 0)
    (v : Fin 2 → ℝ) {w : Fin 2 → ℝ} (hw : w = ![0, -(m * g)]) :
    Constrained.multiplier (pendulumConstraint x) (pendulumInertia m x) w
        (pendulumConstraint v *ᵥ v) =
      fun _ => m / (x 0 ^ 2 + x 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2 - g * x 1) := by
  have hs : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := by
    intro h
    apply hx
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.zero_apply]
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    · simp only [Fin.mk_one, Fin.isValue, Pi.zero_apply]
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  set c := m / (x 0 ^ 2 + x 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2 - g * x 1) with hc
  have h : pendulumInertia m x *ᵥ ![-(c * x 0) / m, (-(m * g) - c * x 1) / m] +
      (pendulumConstraint x)ᵀ *ᵥ (fun _ => c) = w := by
    subst hw
    funext i
    fin_cases i <;>
      simp [pendulumInertia, pendulumConstraint, Matrix.mulVec, dotProduct] <;>
      field_simp <;> ring
  symm
  refine (Constrained.add_eq_zero_iff_eq_multiplier (Matrix.PosDef.one.smul hm)
    (pendulumConstraint_linearIndependent hx) h).mp ?_
  funext i
  simp [pendulumConstraint, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc, Matrix.vecHead,
    Matrix.vecTail]
  field_simp
  ring

/-- **MLS Example 6.1, pp. 270–271: eqs. (6.5)–(6.6) for the pendulum.** For `m > 0` and `l > 0`,
along a motion on the circle `x² + y² = l²` near `t` with velocity `θ'` near `t` and acceleration
`θ''` at `t`, the multiplier equations (6.4) with no applied force hold at `t` exactly when
`m q̈ + (0, m g) + (x, y) λ = 0` and `λ = (m / l²)(ẋ² + ẏ² − g y)`, the value of (6.6). MLS prints
`λ = −(m / l²)(g y + ẋ² + ẏ²)` (E034 source observation). -/
theorem pendulum_multiplierEquationsAt_iff {m g l : ℝ} (hm : 0 < m) (hl : 0 < l)
    {θ θ' : ℝ → Fin 2 → ℝ} {θ'' : Fin 2 → ℝ} {t : ℝ}
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t)
    (hc : ∀ᶠ s in 𝓝 t, θ s 0 ^ 2 + θ s 1 ^ 2 = l ^ 2) (μ : Fin 1 → ℝ) :
    Constrained.MultiplierEquationsAt (pendulumLagrangian m g) pendulumConstraint θ 0 μ t ↔
      m • θ'' + ![0, m * g] + μ 0 • θ t = 0 ∧
        μ 0 = m / l ^ 2 * (θ' t 0 ^ 2 + θ' t 1 ^ 2 - g * θ t 1) := by
  have hx : θ t ≠ 0 := by
    intro h0
    have h := hc.self_of_nhds
    rw [h0] at h
    simp only [Pi.zero_apply] at h
    nlinarith
  have hV : HasFDerivAt (pendulumPotential m g)
      ((m * g) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) (θ t) :=
    (hasFDerivAt_apply 1 (θ t)).const_mul (m * g)
  have hM : ∀ i j, HasFDerivAt (fun q => pendulumInertia m q i j)
      (0 : (Fin 2 → ℝ) →L[ℝ] ℝ) (θ t) :=
    fun i j => hasFDerivAt_const _ _
  have hsymm : ∀ q, (pendulumInertia m q).IsSymm := fun _ => Matrix.isSymm_one.smul m
  have hAd : ∀ i j, HasDerivAt (fun s => pendulumConstraint (θ s) i j)
      (pendulumConstraint (θ' t) i j) t :=
    fun _ j => hasDerivAt_pi.mp hθ.self_of_nhds j
  have key := Constrained.multiplierEquationsAt_mechanical_iff_multiplier hsymm hM hV hθ hθ'
    (Matrix.PosDef.one.smul hm) (pendulumConstraint_linearIndependent hx)
    (pendulum_eventually_pfaffianAt hθ hc) hAd 0 0 μ
  rw [sub_zero] at key
  have hw : 0 - Christoffel.coriolisMatrix
        (Christoffel.partials fun _ _ => (0 : (Fin 2 → ℝ) →L[ℝ] ℝ)) (θ' t) *ᵥ θ' t -
      Lagrangian.gradient ((m * g) • ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 2 => ℝ) 1) = ![0, -(m * g)] := by
    rw [coriolisMatrix_partials_zero, Matrix.zero_mulVec]
    funext i
    fin_cases i <;> simp [Lagrangian.gradient]
  rw [pendulumLagrangian, key, add_zero, pendulum_lhs, pendulum_multiplier hm g hx (θ' t) hw,
    hc.self_of_nhds]
  exact and_congr_right fun _ =>
    ⟨fun h => by rw [h], fun h => funext fun i => by rw [Subsingleton.elim i 0, h]⟩

/-- **MLS Example 6.1, p. 271: the equations of motion of the pendulum.** Under the hypotheses of
`pendulum_multiplierEquationsAt_iff`, the Lagrange–d'Alembert equations hold at `t` exactly when
`m q̈ + (0, m g) + (x, y) λ = 0` with `λ = (m / l²)(ẋ² + ẏ² − g y)`. -/
theorem pendulum_lagrangeDAlembertAt_iff {m g l : ℝ} (hm : 0 < m) (hl : 0 < l)
    {θ θ' : ℝ → Fin 2 → ℝ} {θ'' : Fin 2 → ℝ} {t : ℝ}
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t)
    (hc : ∀ᶠ s in 𝓝 t, θ s 0 ^ 2 + θ s 1 ^ 2 = l ^ 2) :
    Constrained.LagrangeDAlembertAt (pendulumLagrangian m g) pendulumConstraint θ 0 t ↔
      m • θ'' + ![0, m * g] + (m / l ^ 2 * (θ' t 0 ^ 2 + θ' t 1 ^ 2 - g * θ t 1)) • θ t = 0 := by
  rw [Constrained.lagrangeDAlembertAt_iff_exists_multiplier]
  constructor
  · rintro ⟨μ, hμ⟩
    obtain ⟨h1, h2⟩ := (pendulum_multiplierEquationsAt_iff hm hl hθ hθ' hc μ).mp hμ
    rwa [h2] at h1
  · intro h
    exact ⟨_, (pendulum_multiplierEquationsAt_iff hm hl hθ hθ' hc fun _ =>
      m / l ^ 2 * (θ' t 0 ^ 2 + θ' t 1 ^ 2 - g * θ t 1)).mpr ⟨h, rfl⟩⟩

/-- **MLS Example 6.1, p. 271: the tension `‖(x, y) λ‖`** (Euclidean norm, written out) on the
circle `x² + y² = l²` with `λ = (m / l²)(ẋ² + ẏ² − g y)` is `(m / l) |ẋ² + ẏ² − g y|`. MLS prints
`(m g / l) y + (m / l)(ẋ² + ẏ²)` (E034 source observation). -/
theorem pendulum_tension {m g l : ℝ} (hm : 0 < m) (hl : 0 < l) {q v : Fin 2 → ℝ}
    (hq : q 0 ^ 2 + q 1 ^ 2 = l ^ 2) :
    Real.sqrt ((q 0 * (m / l ^ 2 * (v 0 ^ 2 + v 1 ^ 2 - g * q 1))) ^ 2 +
        (q 1 * (m / l ^ 2 * (v 0 ^ 2 + v 1 ^ 2 - g * q 1))) ^ 2) =
      m / l * |v 0 ^ 2 + v 1 ^ 2 - g * q 1| := by
  have e : (q 0 * (m / l ^ 2 * (v 0 ^ 2 + v 1 ^ 2 - g * q 1))) ^ 2 +
      (q 1 * (m / l ^ 2 * (v 0 ^ 2 + v 1 ^ 2 - g * q 1))) ^ 2 =
        (m / l * |v 0 ^ 2 + v 1 ^ 2 - g * q 1|) ^ 2 := by
    set E := v 0 ^ 2 + v 1 ^ 2 - g * q 1
    calc (q 0 * (m / l ^ 2 * E)) ^ 2 + (q 1 * (m / l ^ 2 * E)) ^ 2 =
        (m / l ^ 2 * E) ^ 2 * (q 0 ^ 2 + q 1 ^ 2) := by ring
      _ = (m / l * |E|) ^ 2 := by
        rw [hq, mul_pow _ |E|, sq_abs]
        field_simp
  rw [e, Real.sqrt_sq (by positivity)]

/-! ### Example 6.2: the rolling disk (MLS pp. 272–274) -/

/-- **MLS Example 6.2, eq. (6.10), p. 273: the rolling constraint**
`A(q) = [[1, 0, 0, −ρ cos θ], [0, 1, 0, −ρ sin θ]]` for `q = (x, y, θ, φ)` (Lean indices
`0, 1, 2, 3`) and disk radius `ρ`. -/
def rollingDiskConstraint (ρ : ℝ) (q : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 4) ℝ :=
  !![1, 0, 0, -ρ * Real.cos (q 2); 0, 1, 0, -ρ * Real.sin (q 2)]

/-- **MLS Example 6.2, p. 273: the inertia `diag(m, m, I₁, I₂)`** of the rolling disk. -/
def rollingDiskInertia (m I₁ I₂ : ℝ) (_q : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![m, m, I₁, I₂]

/-- **MLS Example 6.2, p. 273: the Lagrangian of the disk,** kinetic energy only, as a mechanical
Lagrangian (MLS eq. (4.20)) with zero potential. -/
def rollingDiskLagrangian (m I₁ I₂ : ℝ) : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ :=
  Lagrangian.mechanical (rollingDiskInertia m I₁ I₂) fun _ => 0

/-- **MLS Example 6.2, p. 273: the generalized force `(0, 0, τ_θ, τ_φ)`** of the wheel torques. -/
def rollingDiskForce (τθ τφ : ℝ) : Fin 4 → ℝ :=
  ![0, 0, τθ, τφ]

/-- **MLS Example 6.2, p. 273: "The Lagrangian is
`L(q, q̇) = ½ m (ẋ² + ẏ²) + ½ I₁ θ̇² + ½ I₂ φ̇²`."** -/
theorem rollingDiskLagrangian_apply (m I₁ I₂ : ℝ) (q v : Fin 4 → ℝ) :
    rollingDiskLagrangian m I₁ I₂ q v =
      1 / 2 * m * (v 0 ^ 2 + v 1 ^ 2) + 1 / 2 * I₁ * v 2 ^ 2 + 1 / 2 * I₂ * v 3 ^ 2 := by
  simp [rollingDiskLagrangian, Lagrangian.mechanical, rollingDiskInertia, dotProduct,
    Fin.sum_univ_four, Matrix.mulVec_diagonal]
  ring

/-- **MLS Example 6.2, p. 273: "The constraints are everywhere linearly independent."** -/
theorem rollingDiskConstraint_linearIndependent (ρ : ℝ) (q : Fin 4 → ℝ) :
    LinearIndependent ℝ (rollingDiskConstraint ρ q).row := by
  refine Constrained.linearIndependent_row_of_isUnit_det ![0, 1] ?_
  simp [rollingDiskConstraint, Matrix.det_fin_two]

/-- **MLS Example 6.2, eq. (6.11), p. 273: the virtual displacements of the rolling disk,**
`A(q) δq = 0 ⇔ δx = ρ cos θ δφ ∧ δy = ρ sin θ δφ`. -/
theorem rollingDisk_virtual_iff (ρ : ℝ) (q δq : Fin 4 → ℝ) :
    rollingDiskConstraint ρ q *ᵥ δq = 0 ↔
      δq 0 = ρ * Real.cos (q 2) * δq 3 ∧ δq 1 = ρ * Real.sin (q 2) * δq 3 := by
  simp only [funext_iff, Fin.forall_fin_two, rollingDiskConstraint, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four]
  simp
  constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith

/-- **MLS Example 6.2, eq. (6.12), p. 274: the Lagrange–d'Alembert equations of the rolling disk.**
Along a motion `q` with velocity `q'` near `t` and acceleration `q''` at `t`, (6.7)–(6.8) hold at
`t` exactly when `I₁ θ̈ = τ_θ` and `m ρ cos θ ẍ + m ρ sin θ ÿ + I₂ φ̈ = τ_φ`. -/
theorem rollingDisk_lagrangeDAlembertAt_iff {m I₁ I₂ ρ τθ τφ : ℝ} {q q' : ℝ → Fin 4 → ℝ}
    {q'' : Fin 4 → ℝ} {t : ℝ} (hq : ∀ᶠ s in 𝓝 t, HasDerivAt q (q' s) s)
    (hq' : HasDerivAt q' q'' t) :
    Constrained.LagrangeDAlembertAt (rollingDiskLagrangian m I₁ I₂) (rollingDiskConstraint ρ) q
        (rollingDiskForce τθ τφ) t ↔
      I₁ * q'' 2 = τθ ∧
        m * ρ * Real.cos (q t 2) * q'' 0 + m * ρ * Real.sin (q t 2) * q'' 1 + I₂ * q'' 3 = τφ := by
  have hM : ∀ i j, HasFDerivAt (fun x => rollingDiskInertia m I₁ I₂ x i j)
      (0 : (Fin 4 → ℝ) →L[ℝ] ℝ) (q t) := fun _ _ => hasFDerivAt_const _ _
  have hV : HasFDerivAt (fun _ : Fin 4 → ℝ => (0 : ℝ)) (0 : (Fin 4 → ℝ) →L[ℝ] ℝ) (q t) :=
    hasFDerivAt_const _ _
  have hsymm : ∀ x, (rollingDiskInertia m I₁ I₂ x).IsSymm := fun _ => Matrix.isSymm_diagonal _
  have hR : rollingDiskInertia m I₁ I₂ (q t) *ᵥ q'' + Lagrangian.gradient 0 -
      rollingDiskForce τθ τφ = ![m * q'' 0, m * q'' 1, I₁ * q'' 2 - τθ, I₂ * q'' 3 - τφ] := by
    funext i
    fin_cases i <;>
      simp [rollingDiskInertia, rollingDiskForce, Lagrangian.gradient, Matrix.mulVec_diagonal]
  rw [rollingDiskLagrangian, Constrained.lagrangeDAlembertAt_mechanical_iff hsymm hM hV hq hq',
    coriolisMatrix_partials_zero, Matrix.zero_mulVec, add_zero, hR]
  constructor
  · intro h
    have h1 := h ![0, 0, 1, 0] ((rollingDisk_virtual_iff ρ (q t) _).mpr (by simp))
    have h2 := h ![ρ * Real.cos (q t 2), ρ * Real.sin (q t 2), 0, 1]
      ((rollingDisk_virtual_iff ρ (q t) _).mpr (by simp))
    simp [dotProduct, Fin.sum_univ_four] at h1 h2
    exact ⟨by linear_combination h1, by linear_combination h2⟩
  · rintro ⟨h1, h2⟩ δq hδ
    obtain ⟨e0, e1⟩ := (rollingDisk_virtual_iff ρ (q t) δq).mp hδ
    simp only [dotProduct, Fin.sum_univ_four]
    simp
    rw [e0, e1]
    linear_combination δq 2 * h1 + δq 3 * h2

/-- **MLS Example 6.2, eq. (6.13), p. 274: "Differentiating the constraints"**,
`ẍ = ρ cos θ φ̈ − ρ sin θ θ̇ φ̇` and `ÿ = ρ sin θ φ̈ + ρ cos θ θ̇ φ̇`, along a motion that satisfies
the rolling constraint near `t`, with velocity `q'` near `t` and acceleration `q''` at `t`. -/
theorem rollingDisk_acceleration {ρ : ℝ} {q q' : ℝ → Fin 4 → ℝ} {q'' : Fin 4 → ℝ} {t : ℝ}
    (hq : ∀ᶠ s in 𝓝 t, HasDerivAt q (q' s) s) (hq' : HasDerivAt q' q'' t)
    (hc : ∀ᶠ s in 𝓝 t, Constrained.PfaffianAt (rollingDiskConstraint ρ) (q s) (q' s)) :
    q'' 0 = ρ * Real.cos (q t 2) * q'' 3 - ρ * Real.sin (q t 2) * q' t 2 * q' t 3 ∧
      q'' 1 = ρ * Real.sin (q t 2) * q'' 3 + ρ * Real.cos (q t 2) * q' t 2 * q' t 3 := by
  have h2 : HasDerivAt (fun s => q s 2) (q' t 2) t := hasDerivAt_pi.mp hq.self_of_nhds 2
  have hcos : HasDerivAt (fun s => -(ρ * Real.cos (q s 2))) (ρ * Real.sin (q t 2) * q' t 2) t := by
    convert (h2.cos.const_mul ρ).neg using 1
    ring
  have hsin : HasDerivAt (fun s => -(ρ * Real.sin (q s 2)))
      (-(ρ * Real.cos (q t 2) * q' t 2)) t := by
    convert (h2.sin.const_mul ρ).neg using 1
    ring
  have hAd : ∀ i j, HasDerivAt (fun s => rollingDiskConstraint ρ (q s) i j)
      (!![0, 0, 0, ρ * Real.sin (q t 2) * q' t 2; 0, 0, 0, -(ρ * Real.cos (q t 2) * q' t 2)] i j)
      t := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [rollingDiskConstraint] <;> simp <;>
      first | exact hasDerivAt_const _ _ | exact hcos | exact hsin
  have hd := Constrained.mulVec_add_mulVec_eq_zero hc hAd hq'
  have d0 := congrFun hd 0
  have d1 := congrFun hd 1
  simp [rollingDiskConstraint, dotProduct, Fin.sum_univ_four] at d0 d1
  exact ⟨by linear_combination d0, by linear_combination d1⟩

/-- **MLS Example 6.2, eq. (6.14), p. 274: the reduced equations of the rolling disk.** Along a
motion that satisfies the rolling constraint near `t`, with velocity `q'` near `t` and acceleration
`q''` at `t`, the Lagrange–d'Alembert equations hold at `t` exactly when
`diag(I₁, I₂ + m ρ²) (θ̈, φ̈) = (τ_θ, τ_φ)`. -/
theorem rollingDisk_lagrangeDAlembertAt_iff_reduced {m I₁ I₂ ρ τθ τφ : ℝ} {q q' : ℝ → Fin 4 → ℝ}
    {q'' : Fin 4 → ℝ} {t : ℝ} (hq : ∀ᶠ s in 𝓝 t, HasDerivAt q (q' s) s)
    (hq' : HasDerivAt q' q'' t)
    (hc : ∀ᶠ s in 𝓝 t, Constrained.PfaffianAt (rollingDiskConstraint ρ) (q s) (q' s)) :
    Constrained.LagrangeDAlembertAt (rollingDiskLagrangian m I₁ I₂) (rollingDiskConstraint ρ) q
        (rollingDiskForce τθ τφ) t ↔
      I₁ * q'' 2 = τθ ∧ (I₂ + m * ρ ^ 2) * q'' 3 = τφ := by
  obtain ⟨a0, a1⟩ := rollingDisk_acceleration hq hq' hc
  have e : m * ρ * Real.cos (q t 2) * q'' 0 + m * ρ * Real.sin (q t 2) * q'' 1 + I₂ * q'' 3 =
      (I₂ + m * ρ ^ 2) * q'' 3 := by
    rw [a0, a1]
    linear_combination m * ρ ^ 2 * q'' 3 * Real.sin_sq_add_cos_sq (q t 2)
  rw [rollingDisk_lagrangeDAlembertAt_iff hq hq', e]

end Examples
end RoboLean
