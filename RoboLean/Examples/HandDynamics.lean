import RoboLean.Dynamics.CompositeDynamics

/-!
# Hand–object instances of MLS §2 (eqs. (6.18)–(6.26), Lemma 6.1)

MLS Chapter 6, §2, printed pp. 276–284. Two small systems that satisfy every hypothesis of
`RoboLean.Dynamics.CompositeDynamics`, with `J_h` invertible (MLS assumption 2, p. 277):

* **Two prismatic fingers squeezing a block on a line** (`n = 2`, `p = 1`, `q = (θ₁, θ₂, x)` in
  MLS's ordering `q = (θ, x)`): each fingertip moves with the block, `θ̇₁ = ẋ`, `θ̇₂ = ẋ`, so
  `J_h = I` and `Gᵀ = (1, 1)`; finger masses `m₁`, `m₂`, block mass `m_o`, no potential. The
  effective mass is `m_o + m₁ + m₂`, the effective force `τ₁ + τ₂`, the squeeze `τ = (1, −1)` is an
  internal force (`G J_h⁻ᵀ τ = 0`, p. 280), and along every motion satisfying the grasp constraint
  the Lagrange–d'Alembert equations are `(m_o + m₁ + m₂) ẍ = τ₁ + τ₂`.
* **A revolute finger pushing a slider** (`n = p = 1`), the workspace setting of (6.26) with an
  object: the fingertip abscissa `l sin θ` equals the slider position `x`, so `J = l cos θ` and
  `G = I`; the effective mass is `m_o + I / (l cos θ)²`, positive definite for `m_o > 0` at every
  configuration, and, for `I > 0`, growing without bound as `cos θ → 0` (p. 283's singular
  configurations).

The SCARA hand of MLS Example 5.6 (E028, G27) is not an instance: with the object pose of the
example its hand Jacobian is not onto at any finger configuration
(`Examples.scaraHand_graspTranspose_rotY_not_mem_range`), so it is not invertible. These are
mathematical instances; nothing here models a physical hand.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Examples

open Constrained Composite

/-! ### Two prismatic fingers squeezing a block -/

/-- **MLS p. 277, (6.18), for two prismatic fingers on a block:** the hand Jacobian `J_h = I`. -/
def squeezeHandJacobian (_q : Fin (2 + 1) → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  1

/-- **MLS p. 277, (6.18), for two prismatic fingers on a block:** the grasp matrix `G = [1 1]`, so
`Gᵀ ẋ = (ẋ, ẋ)`. -/
def squeezeGrasp (_q : Fin (2 + 1) → ℝ) : Matrix (Fin 1) (Fin 2) ℝ :=
  !![1, 1]

/-- **MLS p. 276, (6.16): the finger inertia `diag(m₁, m₂)`** of two prismatic fingers. -/
def squeezeFingerInertia (m₁ m₂ : ℝ) (_θ : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![m₁, m₂]

/-- **MLS p. 277: the object inertia `[m_o]`** of a block on a line. -/
def squeezeObjectInertia (mo : ℝ) (_x : Fin 1 → ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  !![mo]

/-- **MLS eq. (6.18), p. 277, for the squeeze:** `[J_h −Gᵀ] q̇ = 0` exactly when `θ̇₁ = ẋ` and
`θ̇₂ = ẋ` (`q = (θ₁, θ₂, x)`). -/
theorem squeeze_pfaffianAt_iff (q v : Fin (2 + 1) → ℝ) :
    PfaffianAt (handPfaffian (mlsSplit 1 2) squeezeHandJacobian squeezeGrasp) q v ↔
      v 0 = v 2 ∧ v 1 = v 2 := by
  rw [pfaffianAt_handPfaffian_iff, funext_iff, Fin.forall_fin_two]
  simp [squeezeHandJacobian, squeezeGrasp, splitFst, splitSnd, mlsSplit, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  rfl

/-- **MLS eq. (6.22), p. 278, for the squeeze:** `M̃ = m_o + m₁ + m₂`. -/
theorem squeeze_effectiveMass (mo m₁ m₂ : ℝ) (q : Fin (2 + 1) → ℝ) (x : Fin 1 → ℝ)
    (θ : Fin 2 → ℝ) :
    effectiveMass (squeezeObjectInertia mo x) (squeezeFingerInertia m₁ m₂ θ)
        (squeezeHandJacobian q) (squeezeGrasp q) = !![mo + m₁ + m₂] := by
  ext i j
  fin_cases i
  fin_cases j
  simp [effectiveMass, squeezeObjectInertia, squeezeFingerInertia, squeezeHandJacobian,
    squeezeGrasp, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.diagonal_apply]
  ring

/-- **MLS eq. (6.22), p. 278, for the squeeze:** `F = G J_h⁻ᵀ τ = τ₁ + τ₂`. -/
theorem squeeze_effectiveForce (q : Fin (2 + 1) → ℝ) (τ : Fin 2 → ℝ) :
    effectiveForce (squeezeHandJacobian q) (squeezeGrasp q) τ = ![τ 0 + τ 1] := by
  funext i
  fin_cases i
  simp [effectiveForce, squeezeHandJacobian, squeezeGrasp, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.mul_apply]

/-- **MLS p. 280: "If `J_h⁻ᵀ τ ∈ N(G)`, then no net wrench is generated"** — the squeeze
`τ = (1, −1)` produces no force on the block, an internal force. -/
theorem squeeze_internalForce (q : Fin (2 + 1) → ℝ) :
    effectiveForce (squeezeHandJacobian q) (squeezeGrasp q) ![1, -1] = 0 := by
  rw [squeeze_effectiveForce]
  funext i
  fin_cases i
  simp

private theorem coriolisMatrix_partials_zero' {k : ℕ} (v : Fin k → ℝ) :
    Christoffel.coriolisMatrix (Christoffel.partials 0) v = 0 := by
  ext i j
  simp [Christoffel.coriolisMatrix, Christoffel.symbol, Christoffel.partials]

private theorem splitFst_mlsSplit (v : Fin (2 + 1) → ℝ) : splitFst (mlsSplit 1 2) v = ![v 2] := by
  funext a
  fin_cases a
  rfl

private theorem splitSnd_mlsSplit (v : Fin (2 + 1) → ℝ) :
    splitSnd (mlsSplit 1 2) v = ![v 0, v 1] := by
  funext b
  fin_cases b <;> rfl

/-- **MLS eqs. (6.19)–(6.22), pp. 278, for the squeeze:** along a motion `q = (θ₁, θ₂, x)` with
velocity `q'` near `t` and acceleration `q''` at `t` that satisfies the grasp constraint near `t`,
the Lagrange–d'Alembert equations of the composite system with joint torques `τ` hold at `t` exactly
when `(m_o + m₁ + m₂) ẍ = τ₁ + τ₂`. -/
theorem squeeze_lagrangeDAlembertAt_iff (mo m₁ m₂ : ℝ) {q q' : ℝ → Fin (2 + 1) → ℝ}
    {q'' : Fin (2 + 1) → ℝ} {t : ℝ} (hq : ∀ᶠ s in 𝓝 t, HasDerivAt q (q' s) s)
    (hq' : HasDerivAt q' q'' t)
    (hc : ∀ᶠ s in 𝓝 t,
      PfaffianAt (handPfaffian (mlsSplit 1 2) squeezeHandJacobian squeezeGrasp) (q s) (q' s))
    (τ : Fin 2 → ℝ) :
    LagrangeDAlembertAt
        (lagrangian (mlsSplit 1 2) (Lagrangian.mechanical (squeezeObjectInertia mo) fun _ => 0)
          (Lagrangian.mechanical (squeezeFingerInertia m₁ m₂) fun _ => 0))
        (handPfaffian (mlsSplit 1 2) squeezeHandJacobian squeezeGrasp) q
        (handForce (mlsSplit 1 2) τ) t ↔
      (mo + m₁ + m₂) * q'' 2 = τ 0 + τ 1 := by
  have hMo : ∀ (y : Fin 1 → ℝ) i j,
      HasFDerivAt (fun y => squeezeObjectInertia mo y i j) (0 : (Fin 1 → ℝ) →L[ℝ] ℝ) y :=
    fun y i j => hasFDerivAt_const _ y
  have hMf : ∀ (y : Fin 2 → ℝ) i j,
      HasFDerivAt (fun y => squeezeFingerInertia m₁ m₂ y i j) (0 : (Fin 2 → ℝ) →L[ℝ] ℝ) y :=
    fun y i j => hasFDerivAt_const _ y
  have hB : ∀ i j, HasDerivAt
      (fun s => ((squeezeHandJacobian (q s))⁻¹ * (squeezeGrasp (q s))ᵀ) i j) (0 : ℝ) t :=
    fun i j => by
      simp only [squeezeHandJacobian, squeezeGrasp]
      exact hasDerivAt_const t _
  have hJ : ∀ᶠ s in 𝓝 t, IsUnit (squeezeHandJacobian (q s)).det :=
    Filter.Eventually.of_forall fun s => by simp [squeezeHandJacobian]
  rw [lagrangeDAlembertAt_handPfaffian_iff_effective (mlsSplit 1 2)
    (Mo' := 0) (Mf' := 0) (Vo' := 0) (Vf' := 0) (Bd := 0)
    (fun _ => Matrix.IsSymm.ext fun i j => by fin_cases i; fin_cases j; rfl)
    (fun _ => by simp [squeezeFingerInertia])
    (hMo _) (hasFDerivAt_const _ _) (hMf _) (hasFDerivAt_const _ _) hq hq' hc hJ
    (fun i j => by simpa using hB i j) τ]
  rw [squeeze_effectiveMass, squeeze_effectiveForce]
  simp only [splitFst_mlsSplit, splitSnd_mlsSplit, coriolisMatrix_partials_zero']
  simp [effectiveCoriolis, effectiveN, Lagrangian.gradient, Matrix.mulVec, dotProduct, funext_iff,
    mul_comm]

/-! ### A revolute finger pushing a slider (eq. (6.26) with an object) -/

/-- **MLS p. 282: the Jacobian `J = ∂g/∂θ = l cos θ`** of the fingertip abscissa `g(θ) = l sin θ` of
a revolute finger of length `l`. -/
def sliderJacobian (l θ : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  !![l * Real.cos θ]

/-- **MLS eq. (6.26), p. 283, for the slider:** with `G = I`, finger inertia `[I]` and slider mass
`m_o`, `M̃ = m_o + I / (l cos θ)²` at every configuration with `l cos θ ≠ 0`. -/
theorem slider_effectiveMass {mo I l θ : ℝ} (h : l * Real.cos θ ≠ 0) :
    effectiveMass !![mo] !![I] (sliderJacobian l θ) 1 = !![mo + I / (l * Real.cos θ) ^ 2] := by
  have hl : l ≠ 0 := left_ne_zero_of_mul h
  have hc : Real.cos θ ≠ 0 := right_ne_zero_of_mul h
  have hinv : (sliderJacobian l θ)⁻¹ = !![(l * Real.cos θ)⁻¹] := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i
    fin_cases j
    simp [sliderJacobian]
    field_simp
  rw [effectiveMass_one, hinv]
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply]
  field_simp

/-- **MLS p. 283 for the slider: "`M̃ > 0`"** at every configuration, singular ones included, when
the slider mass is positive and the finger inertia nonnegative (`effectiveMass_posDef`). -/
theorem slider_effectiveMass_posDef {mo I : ℝ} (hmo : 0 < mo) (hI : 0 ≤ I) (l θ : ℝ) :
    (effectiveMass !![mo] !![I] (sliderJacobian l θ) 1).PosDef := by
  refine effectiveMass_posDef ?_ ?_ _ _
  · rw [show (!![mo] : Matrix (Fin 1) (Fin 1) ℝ) = Matrix.diagonal ![mo] by
      ext i j; fin_cases i; fin_cases j; rfl]
    exact Matrix.posDef_diagonal_iff.mpr fun i => by fin_cases i; simpa using hmo
  · rw [show (!![I] : Matrix (Fin 1) (Fin 1) ℝ) = Matrix.diagonal ![I] by
      ext i j; fin_cases i; fin_cases j; rfl]
    exact Matrix.posSemidef_diagonal_iff.mpr fun i => by fin_cases i; simpa using hI

end Examples
end RoboLean
