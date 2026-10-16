import RoboLean.Dynamics.RedundantDynamics
import RoboLean.Dynamics.Tendons

/-!
# Examples 6.3–6.5: a redundant planar arm and tendon-driven fingers

MLS Chapter 6, Example 6.3 (printed pp. 287–289, Figure 6.5), Example 6.4 (pp. 296, Figure 6.9),
Example 6.5 (p. 298, Figure 6.10), and the tendon counts of p. 299.
Lean indices `0, 1, 2` stand for the book's `θ₁, θ₂, θ₃`; tendons `0, …, 3` for the book's
`1, …, 4`.

**Example 6.3, the three-link planar manipulator with unit links.** The end-effector position
`(x, y) = (Σ cos θᵢ, Σ sin θᵢ)` (link angles measured from a fixed axis) has the printed Jacobian
(`jac_threeLinkPosition`). The first choice `K = [0 0 1]` completes `J` to an invertible matrix
exactly when `sin(θ₂ − θ₁) ≠ 0` (`det_threeLink_augmentedJacobian_completion`; the book says "as
long as `θ₁ ≠ θ₂` (i.e., when the first two links are not aligned)"), but its row is never in `N(J)`
(`threeLinkJacobian_mul_completion_transpose_ne_zero`): it is a completion, not a basis of the null
space. The second choice `K = [sin(θ₂ − θ₃) −sin(θ₁ − θ₃) sin(θ₁ − θ₂)]` (p. 288) satisfies
`J Kᵀ = 0` (`threeLinkJacobian_mul_nullRow_transpose`),
`det J̄ = −(sin²(θ₂ − θ₃) + sin²(θ₁ − θ₃) + sin²(θ₁ − θ₂))`
(`det_threeLink_augmentedJacobian_nullRow`), so `J̄` is invertible exactly when the three links are
not all aligned (`isUnit_det_threeLink_nullRow_iff`), and it is not the differential of any `C²`
function (`not_exists_contDiff_fderiv_eq_nullRow`, "there is no `h` such that `∂h/∂θ = K`"). The
third row of `J̄` printed on p. 289 differs from this `K` in its second entry (source
observation O9 in the coverage ledger).

**Example 6.5, elastic tendons (p. 298).** For the linear extension functions of Figure 6.10 the
coupling matrix is the printed constant `P` (`couplingMatrix_elasticFinger`), the stiffness is the
printed `S(θ)` (`tendonStiffness_elasticFinger`) and `Q = P K` is the printed matrix
(`couplingMatrix_mul_diagonal_elasticFinger`).

**Example 6.4, the two-link tendon-driven finger (p. 296).** For the printed extension functions
(the branch `θ₁ > 0`) the coupling matrix is the printed `P(θ)` (`couplingMatrix_tendonFinger`), and
for positive pulley radii the network is force-closure (`isTendonForceClosure_tendonFinger`; the
"2N" configuration of p. 299).

**A two-tendon finger.** One revolute joint driven by two antagonistic tendons of pulley radius
`r ≠ 0` is force-closure with `2 = n + 1 = 2n` tendons (`isTendonForceClosure_twoTendon`), the
bounds of p. 299 attained.

These are mathematical instances on concrete inputs; nothing here models a physical finger.
-/

noncomputable section

open Matrix Real

namespace RoboLean
namespace Examples

open Composite

/-! ### Example 6.3: the three-link planar manipulator (MLS pp. 287–289) -/

/-- **The end-effector position of the three-link planar manipulator with unit-length links (MLS
Example 6.3, printed p. 287):** `x = cos θ₁ + cos θ₂ + cos θ₃`, `y = sin θ₁ + sin θ₂ + sin θ₃`, link
angles measured from a fixed axis (Figure 6.5). -/
def threeLinkPosition (θ : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![cos (θ 0) + cos (θ 1) + cos (θ 2), sin (θ 0) + sin (θ 1) + sin (θ 2)]

/-- **The Jacobian printed in MLS Example 6.3, p. 288:**
`J(θ) = [[−sin θ₁, −sin θ₂, −sin θ₃], [cos θ₁, cos θ₂, cos θ₃]]`. -/
def threeLinkJacobian (θ : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![-sin (θ 0), -sin (θ 1), -sin (θ 2); cos (θ 0), cos (θ 1), cos (θ 2)]

/-- **MLS Example 6.3, p. 288: "The Jacobian of the mapping `θ ↦ (x, y)` is" the printed `J(θ)`**
(`MapJacobian.jac`). -/
theorem jac_threeLinkPosition (θ : Fin 3 → ℝ) :
    MapJacobian.jac threeLinkPosition θ = threeLinkJacobian θ := by
  have hc : ∀ k : Fin 3, HasFDerivAt (fun x : Fin 3 → ℝ => cos (x k))
      (-sin (θ k) • ContinuousLinearMap.proj k) θ :=
    fun k => by
      have h := (hasDerivAt_cos (θ k)).comp_hasFDerivAt θ (hasFDerivAt_apply (𝕜 := ℝ) k θ)
      exact h
  have hs : ∀ k : Fin 3, HasFDerivAt (fun x : Fin 3 → ℝ => sin (x k))
      (cos (θ k) • ContinuousLinearMap.proj k) θ :=
    fun k => by
      have h := (hasDerivAt_sin (θ k)).comp_hasFDerivAt θ (hasFDerivAt_apply (𝕜 := ℝ) k θ)
      exact h
  have hL : ∀ i, HasFDerivAt (fun x => threeLinkPosition x i)
      ((![-sin (θ 0) • ContinuousLinearMap.proj 0 + -sin (θ 1) • ContinuousLinearMap.proj 1 +
          -sin (θ 2) • ContinuousLinearMap.proj 2,
        cos (θ 0) • ContinuousLinearMap.proj 0 + cos (θ 1) • ContinuousLinearMap.proj 1 +
          cos (θ 2) • ContinuousLinearMap.proj 2] : Fin 2 → (Fin 3 → ℝ) →L[ℝ] ℝ) i) θ := by
    intro i
    fin_cases i
    · exact ((hc 0).add (hc 1)).add (hc 2)
    · exact ((hs 0).add (hs 1)).add (hs 2)
  ext i j
  rw [MapJacobian.jac_apply_of_hasFDerivAt hL]
  fin_cases i <;> fin_cases j <;> simp [threeLinkJacobian]

/-- **The first choice of MLS Example 6.3, p. 288: `K(θ) = [0 0 1]`.** -/
def threeLinkCompletion (_θ : Fin 3 → ℝ) : Matrix (Fin 1) (Fin 3) ℝ :=
  !![0, 0, 1]

/-- **The second choice of MLS Example 6.3, p. 288:
`K(θ) = [sin(θ₂ − θ₃) −sin(θ₁ − θ₃) sin(θ₁ − θ₂)]`.** -/
def threeLinkNullRow (θ : Fin 3 → ℝ) : Matrix (Fin 1) (Fin 3) ℝ :=
  !![sin (θ 1 - θ 2), -sin (θ 0 - θ 2), sin (θ 0 - θ 1)]

/-- `J̄ = [J; K]` for a `2 × 3` matrix `J` and a row `K`, rows in the printed order. -/
private theorem augmentedJacobian_fin_three (J : Matrix (Fin 2) (Fin 3) ℝ)
    (K : Matrix (Fin 1) (Fin 3) ℝ) :
    augmentedJacobian finSumFinEquiv J K =
      !![J 0 0, J 0 1, J 0 2; J 1 0, J 1 1, J 1 2; K 0 0, K 0 1, K 0 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **MLS Example 6.3, p. 288: with `K = [0 0 1]`, `det [J; K] = sin(θ₂ − θ₁)`**, so the choice is
valid exactly when `sin(θ₂ − θ₁) ≠ 0` (the book: "as long as `θ₁ ≠ θ₂` (i.e., when the first two
links are not aligned)"). Rows of `J̄` in the printed order (`finSumFinEquiv`). -/
theorem det_threeLink_augmentedJacobian_completion (θ : Fin 3 → ℝ) :
    (augmentedJacobian finSumFinEquiv (threeLinkJacobian θ) (threeLinkCompletion θ)).det =
      sin (θ 1 - θ 0) := by
  rw [augmentedJacobian_fin_three, det_fin_three, sin_sub]
  simp [threeLinkJacobian, threeLinkCompletion]
  ring

/-- **MLS Example 6.3, p. 288: the row `[0 0 1]` is never in the null space of `J(θ)`**:
`J Kᵀ = (−sin θ₃, cos θ₃) ≠ 0`. It completes `J` to an invertible matrix but does not span `N(J)`
(p. 286). -/
theorem threeLinkJacobian_mul_completion_transpose_ne_zero (θ : Fin 3 → ℝ) :
    threeLinkJacobian θ * (threeLinkCompletion θ)ᵀ ≠ 0 := by
  intro h
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 0
  simp [threeLinkJacobian, threeLinkCompletion, Matrix.mul_apply, Fin.sum_univ_three] at h0 h1
  have h2 := sin_sq_add_cos_sq (θ 2)
  rw [h0, h1] at h2
  norm_num at h2

/-- **MLS Example 6.3, p. 288: the second `K(θ)` lies in the null space of `J(θ)`**, `J Kᵀ = 0`. -/
theorem threeLinkJacobian_mul_nullRow_transpose (θ : Fin 3 → ℝ) :
    threeLinkJacobian θ * (threeLinkNullRow θ)ᵀ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [threeLinkJacobian, threeLinkNullRow, Matrix.mul_apply, Fin.sum_univ_three, sin_sub] <;>
    ring

/-- **MLS Example 6.3, p. 289: `J̄ = [J(θ); K(θ)]`** with the second `K` of p. 288, rows in the
printed order. (The third row printed on p. 289 reads `sin(θ₃ − θ₂)` in place of `−sin(θ₁ − θ₃)`,
source observation O9 in the coverage ledger.) -/
theorem threeLink_augmentedJacobian_nullRow (θ : Fin 3 → ℝ) :
    augmentedJacobian finSumFinEquiv (threeLinkJacobian θ) (threeLinkNullRow θ) =
      !![-sin (θ 0), -sin (θ 1), -sin (θ 2); cos (θ 0), cos (θ 1), cos (θ 2);
        sin (θ 1 - θ 2), -sin (θ 0 - θ 2), sin (θ 0 - θ 1)] := by
  rw [augmentedJacobian_fin_three]
  rfl

/-- **The determinant of `J̄` for the second `K` of MLS Example 6.3, p. 288:**
`det J̄ = −(sin²(θ₂ − θ₃) + sin²(θ₁ − θ₃) + sin²(θ₁ − θ₂))`. -/
theorem det_threeLink_augmentedJacobian_nullRow (θ : Fin 3 → ℝ) :
    (augmentedJacobian finSumFinEquiv (threeLinkJacobian θ) (threeLinkNullRow θ)).det =
      -(sin (θ 1 - θ 2) ^ 2 + sin (θ 0 - θ 2) ^ 2 + sin (θ 0 - θ 1) ^ 2) := by
  rw [threeLink_augmentedJacobian_nullRow, det_fin_three]
  simp [sin_sub]
  ring

/-- **MLS Example 6.3, p. 288: the second `K(θ)` "is valid as long as all three links are not
aligned"**: `J̄` is invertible exactly when not all of `sin(θ₂ − θ₃)`, `sin(θ₁ − θ₃)`,
`sin(θ₁ − θ₂)` vanish (aligned meaning parallel or antiparallel). -/
theorem isUnit_det_threeLink_nullRow_iff (θ : Fin 3 → ℝ) :
    IsUnit (augmentedJacobian finSumFinEquiv (threeLinkJacobian θ) (threeLinkNullRow θ)).det ↔
      ¬ (sin (θ 1 - θ 2) = 0 ∧ sin (θ 0 - θ 2) = 0 ∧ sin (θ 0 - θ 1) = 0) := by
  rw [isUnit_iff_ne_zero, det_threeLink_augmentedJacobian_nullRow]
  constructor
  · rintro h ⟨h1, h2, h3⟩
    apply h
    rw [h1, h2, h3]
    norm_num
  · intro h hz
    apply h
    have h1 : sin (θ 1 - θ 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (sin (θ 1 - θ 2)), sq_nonneg (sin (θ 0 - θ 2)),
        sq_nonneg (sin (θ 0 - θ 1))]
    have h2 : sin (θ 0 - θ 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (sin (θ 1 - θ 2)), sq_nonneg (sin (θ 0 - θ 2)),
        sq_nonneg (sin (θ 0 - θ 1))]
    have h3 : sin (θ 0 - θ 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (sin (θ 1 - θ 2)), sq_nonneg (sin (θ 0 - θ 2)),
        sq_nonneg (sin (θ 0 - θ 1))]
    exact ⟨pow_eq_zero_iff two_ne_zero |>.mp h1, pow_eq_zero_iff two_ne_zero |>.mp h2,
      pow_eq_zero_iff two_ne_zero |>.mp h3⟩

/-- **MLS Example 6.3, p. 288: "Hence, there is no `h` such that `∂h/∂θ = K`"** for the second
`K(θ)`: no twice continuously differentiable `h : ℝ³ → ℝ` has `∂h/∂θᵢ = Kᵢ(θ)` at every `θ`, since
`∂K₁/∂θ₂ = cos(θ₂ − θ₃) ≠ −cos(θ₁ − θ₃) = ∂K₂/∂θ₁` while the mixed partials of `h` commute. -/
theorem not_exists_contDiff_fderiv_eq_nullRow :
    ¬ ∃ h : (Fin 3 → ℝ) → ℝ, ContDiff ℝ 2 h ∧
      ∀ θ (i : Fin 3), fderiv ℝ h θ (Pi.single i 1) = threeLinkNullRow θ 0 i := by
  rintro ⟨h, hh, hK⟩
  have hdiff : Differentiable ℝ h := hh.differentiable (by norm_num)
  have line : ∀ (q v : Fin 3 → ℝ) (c : ℝ), (∀ s : ℝ, fderiv ℝ h (q + s • v) v = c) →
      ∀ s : ℝ, h (q + s • v) = h q + c * s := by
    intro q v c hc s
    have hder : ∀ s : ℝ, HasDerivAt (fun s : ℝ => h (q + s • v) - c * s) 0 s := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ => q + s • v) v s := by
        simpa using ((hasDerivAt_id s).smul_const v).const_add q
      have h2 := ((hdiff (q + s • v)).hasFDerivAt.comp_hasDerivAt s h1).sub
        ((hasDerivAt_id s).const_mul c)
      rw [hc, mul_one, sub_self] at h2
      exact h2
    have h3 := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt)
      (fun s => (hder s).deriv) s 0
    simp only [zero_smul, add_zero, mul_zero, sub_zero] at h3
    linarith
  set a : ℝ := π / 2
  have e3 := line 0 (Pi.single 1 1) 0 (fun s => by rw [hK]; simp [threeLinkNullRow]) a
  have e4 := line 0 (Pi.single 0 1) 0 (fun s => by rw [hK]; simp [threeLinkNullRow]) a
  have e1 := line (a • Pi.single 1 1) (Pi.single 0 1) 1
    (fun s => by rw [hK]; simp [threeLinkNullRow, a]) a
  have e2 := line (a • Pi.single 0 1) (Pi.single 1 1) (-1)
    (fun s => by rw [hK]; simp [threeLinkNullRow, a]) a
  rw [zero_add] at e3 e4
  rw [add_comm] at e1
  have ha : 0 < a := by positivity
  linarith

/-! ### Example 6.5: elastic tendons (MLS p. 298) -/

/-- **The extension functions of MLS Example 6.5, printed p. 298 (Figure 6.10):**
`h₁ = l₁ + r₁₁ θ₁ − r₁₂ θ₂`, `h₂ = l₂ − r₂₁ θ₁`, `h₃ = l₃ + r₃₁ θ₁`, `h₄ = l₄ − r₄₁ θ₁ + r₄₂ θ₂`. -/
def elasticFingerExtension (l : Fin 4 → ℝ) (r₁₁ r₁₂ r₂₁ r₃₁ r₄₁ r₄₂ : ℝ) (θ : Fin 2 → ℝ) :
    Fin 4 → ℝ :=
  ![l 0 + r₁₁ * θ 0 - r₁₂ * θ 1, l 1 - r₂₁ * θ 0, l 2 + r₃₁ * θ 0, l 3 - r₄₁ * θ 0 + r₄₂ * θ 1]

/-- The extension functions of Example 6.5 are affine, `h(θ) = l + R θ` (MLS p. 298). -/
private theorem elasticFingerExtension_eq (l : Fin 4 → ℝ) (r₁₁ r₁₂ r₂₁ r₃₁ r₄₁ r₄₂ : ℝ) :
    elasticFingerExtension l r₁₁ r₁₂ r₂₁ r₃₁ r₄₁ r₄₂ =
      fun θ => l + !![r₁₁, -r₁₂; -r₂₁, 0; r₃₁, 0; -r₄₁, r₄₂] *ᵥ θ := by
  funext θ i
  fin_cases i <;>
    simp [elasticFingerExtension, dotProduct, Fin.sum_univ_two] <;> ring

/-- **MLS Example 6.5, p. 298: "The coupling matrix is"
`[[r₁₁, −r₂₁, r₃₁, −r₄₁], [−r₁₂, 0, 0, r₄₂]]`, constant "since all of the extension functions are
linear".** -/
theorem couplingMatrix_elasticFinger (l : Fin 4 → ℝ) (r₁₁ r₁₂ r₂₁ r₃₁ r₄₁ r₄₂ : ℝ)
    (θ : Fin 2 → ℝ) :
    couplingMatrix (elasticFingerExtension l r₁₁ r₁₂ r₂₁ r₃₁ r₄₁ r₄₂) θ =
      !![r₁₁, -r₂₁, r₃₁, -r₄₁; -r₁₂, 0, 0, r₄₂] := by
  rw [elasticFingerExtension_eq, couplingMatrix_affine]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **MLS Example 6.5, p. 298: the overall stiffness `S(θ) = P K (h(θ) − h(0))`** for
`K = diag(k₁, …, k₄)`, the printed matrix times `θ`. -/
theorem tendonStiffness_elasticFinger (l : Fin 4 → ℝ) (r₁₁ r₁₂ r₂₁ r₃₁ r₄₁ r₄₂ : ℝ)
    (k : Fin 4 → ℝ) (θ : Fin 2 → ℝ) :
    tendonStiffness (couplingMatrix (elasticFingerExtension l r₁₁ r₁₂ r₂₁ r₃₁ r₄₁ r₄₂) θ)
        (Matrix.diagonal k) (elasticFingerExtension l r₁₁ r₁₂ r₂₁ r₃₁ r₄₁ r₄₂) θ =
      !![k 0 * r₁₁ ^ 2 + k 1 * r₂₁ ^ 2 + k 2 * r₃₁ ^ 2 + k 3 * r₄₁ ^ 2,
          -k 0 * r₁₁ * r₁₂ - k 3 * r₄₁ * r₄₂;
        -k 0 * r₁₁ * r₁₂ - k 3 * r₄₁ * r₄₂, k 0 * r₁₂ ^ 2 + k 3 * r₄₂ ^ 2] *ᵥ θ := by
  rw [couplingMatrix_elasticFinger]
  funext i
  fin_cases i <;>
    simp [tendonStiffness, elasticFingerExtension, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Fin.sum_univ_two, Matrix.mul_apply] <;>
    ring

/-- **MLS Example 6.5, p. 298: the coupling matrix between the actuator extension and the joint
torques is `Q = P K = [[k₁ r₁₁, −k₂ r₂₁, k₃ r₃₁, −k₄ r₄₁], [−k₁ r₁₂, 0, 0, k₄ r₄₂]]`.** -/
theorem couplingMatrix_mul_diagonal_elasticFinger (l : Fin 4 → ℝ) (r₁₁ r₁₂ r₂₁ r₃₁ r₄₁ r₄₂ : ℝ)
    (k : Fin 4 → ℝ) (θ : Fin 2 → ℝ) :
    couplingMatrix (elasticFingerExtension l r₁₁ r₁₂ r₂₁ r₃₁ r₄₁ r₄₂) θ * Matrix.diagonal k =
      !![k 0 * r₁₁, -(k 1 * r₂₁), k 2 * r₃₁, -(k 3 * r₄₁); -(k 0 * r₁₂), 0, 0, k 3 * r₄₂] := by
  rw [couplingMatrix_elasticFinger]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_diagonal] <;> ring

/-! ### Example 6.4: a two-link tendon-driven finger (MLS p. 296) -/

/-- **The extension functions of MLS Example 6.4, printed p. 296 (Figure 6.9), branch `θ₁ > 0`:**
`h₁ = l₁ + 2 √(a² + b²) cos(tan⁻¹(a/b) + θ₁/2) − 2b − R₂ θ₂`, `h₂ = l₂ − R₁ θ₁`, `h₃ = l₃ + R₁ θ₁`,
`h₄ = l₄ + R₁ θ₁ + R₂ θ₂` ("When `θ₁ < 0`, these relations are reversed"; the formula is used on all
of `ℝ²` and the book's branch is `θ₁ > 0`). -/
def tendonFingerExtension (l : Fin 4 → ℝ) (a b R₁ R₂ : ℝ) (θ : Fin 2 → ℝ) : Fin 4 → ℝ :=
  ![l 0 + 2 * √(a ^ 2 + b ^ 2) * cos (arctan (a / b) + θ 0 / 2) - 2 * b - R₂ * θ 1,
    l 1 - R₁ * θ 0, l 2 + R₁ * θ 0, l 3 + R₁ * θ 0 + R₂ * θ 1]

/-- **MLS Example 6.4, p. 296: "The coupling matrix for the finger is computed directly from the
extension functions. When `θ₁ > 0`,"
`P(θ) = [[−√(a² + b²) sin(tan⁻¹(a/b) + θ₁/2), −R₁, R₁, R₁], [−R₂, 0, 0, R₂]]`.** -/
theorem couplingMatrix_tendonFinger (l : Fin 4 → ℝ) (a b R₁ R₂ : ℝ) (θ : Fin 2 → ℝ) :
    couplingMatrix (tendonFingerExtension l a b R₁ R₂) θ =
      !![-(√(a ^ 2 + b ^ 2) * sin (arctan (a / b) + θ 0 / 2)), -R₁, R₁, R₁; -R₂, 0, 0, R₂] := by
  have hcos : HasFDerivAt (fun x : Fin 2 → ℝ => cos (arctan (a / b) + x 0 / 2))
      ((-sin (arctan (a / b) + θ 0 / 2) * (1 / 2)) •
        (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ)) θ := by
    have h1 : HasDerivAt (fun s : ℝ => cos (arctan (a / b) + s / 2))
        (-sin (arctan (a / b) + θ 0 / 2) * (1 / 2)) (θ 0) :=
      (hasDerivAt_cos _).comp (θ 0) (((hasDerivAt_id' (θ 0)).div_const 2).const_add _)
    have h2 := h1.comp_hasFDerivAt θ (hasFDerivAt_apply (𝕜 := ℝ) 0 θ)
    exact h2
  have hL : ∀ i, HasFDerivAt (fun x => tendonFingerExtension l a b R₁ R₂ x i)
      ((![(2 * √(a ^ 2 + b ^ 2)) • ((-sin (arctan (a / b) + θ 0 / 2) * (1 / 2)) •
            ContinuousLinearMap.proj 0) - R₂ • ContinuousLinearMap.proj 1,
          -(R₁ • ContinuousLinearMap.proj 0), R₁ • ContinuousLinearMap.proj 0,
          R₁ • ContinuousLinearMap.proj 0 + R₂ • ContinuousLinearMap.proj 1] :
        Fin 4 → (Fin 2 → ℝ) →L[ℝ] ℝ) i) θ := by
    intro i
    fin_cases i
    · exact (((hcos.const_mul (2 * √(a ^ 2 + b ^ 2))).const_add (l 0)).sub_const (2 * b)).sub
        ((hasFDerivAt_apply (𝕜 := ℝ) 1 θ).const_mul R₂)
    · exact ((hasFDerivAt_apply (𝕜 := ℝ) 0 θ).const_mul R₁).const_sub (l 1)
    · exact ((hasFDerivAt_apply (𝕜 := ℝ) 0 θ).const_mul R₁).const_add (l 2)
    · exact (((hasFDerivAt_apply (𝕜 := ℝ) 0 θ).const_mul R₁).const_add (l 3)).add
        ((hasFDerivAt_apply (𝕜 := ℝ) 1 θ).const_mul R₂)
  ext i j
  rw [couplingMatrix, transpose_apply, MapJacobian.jac_apply_of_hasFDerivAt hL]
  fin_cases i <;> fin_cases j <;> simp
  ring

/-- **The tendon network of MLS Example 6.4 is force-closure (eq. (6.34), p. 299; the "2N"
configuration)** for positive pulley radii `R₁`, `R₂`, at every configuration. -/
theorem isTendonForceClosure_tendonFinger (l : Fin 4 → ℝ) (a b : ℝ) {R₁ R₂ : ℝ} (hR₁ : 0 < R₁)
    (hR₂ : 0 < R₂) (θ : Fin 2 → ℝ) :
    IsTendonForceClosure (couplingMatrix (tendonFingerExtension l a b R₁ R₂) θ) := by
  rw [couplingMatrix_tendonFinger, isTendonForceClosure_iff]
  set c := √(a ^ 2 + b ^ 2) * sin (arctan (a / b) + θ 0 / 2)
  have habs := neg_abs_le (c - R₁)
  have hpos : 0 < 1 + |c - R₁| / R₁ := by positivity
  have hpos2 : 0 < 1 + |c - R₁| / R₁ + (c - R₁) / R₁ := by
    have h0 : 0 ≤ (|c - R₁| + (c - R₁)) / R₁ := div_nonneg (by linarith) hR₁.le
    rw [add_assoc, ← add_div]
    linarith
  refine ⟨fun τ => ⟨![0, τ 1 / R₂ - τ 0 / R₁, 0, τ 1 / R₂], ?_⟩,
    ![1, 1 + |c - R₁| / R₁, 1 + |c - R₁| / R₁ + (c - R₁) / R₁, 1], fun i => ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> field_simp
    ring
  · fin_cases i
    exacts [one_pos, hpos, hpos2, one_pos]
  · funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    field_simp
    ring

/-! ### A two-tendon finger: the counts of p. 299 attained -/

/-- **One revolute joint driven by two antagonistic tendons over a pulley of radius `r` (MLS p. 294,
`hᵢ(θ) = lᵢ ± r θ`):** `h(θ) = (l₁ + r θ, l₂ − r θ)`. -/
def twoTendonExtension (l₁ l₂ r : ℝ) (θ : Fin 1 → ℝ) : Fin 2 → ℝ :=
  ![l₁ + r * θ 0, l₂ - r * θ 0]

/-- The two-tendon extension is affine, `h(θ) = l + R θ` (MLS p. 294). -/
private theorem twoTendonExtension_eq (l₁ l₂ r : ℝ) :
    twoTendonExtension l₁ l₂ r = fun θ => ![l₁, l₂] + !![r; -r] *ᵥ θ := by
  funext θ i
  fin_cases i <;> simp [twoTendonExtension, dotProduct]
  ring

/-- **The coupling matrix of the two-tendon finger (MLS p. 295):** `P = [r −r]`. -/
theorem couplingMatrix_twoTendon (l₁ l₂ r : ℝ) (θ : Fin 1 → ℝ) :
    couplingMatrix (twoTendonExtension l₁ l₂ r) θ = !![r, -r] := by
  rw [twoTendonExtension_eq, couplingMatrix_affine]
  ext i j
  fin_cases i
  fin_cases j <;> rfl

/-- **The two-tendon finger is force-closure (MLS eq. (6.34), p. 299) for `r ≠ 0`**, with
`2 = n + 1 = 2n` tendons for `n = 1` joint: the lower bound of Carathéodory's count and the upper
bound of Steinitz's count of p. 299 are both attained. -/
theorem isTendonForceClosure_twoTendon (l₁ l₂ : ℝ) {r : ℝ} (hr : r ≠ 0) (θ : Fin 1 → ℝ) :
    IsTendonForceClosure (couplingMatrix (twoTendonExtension l₁ l₂ r) θ) := by
  rw [couplingMatrix_twoTendon, isTendonForceClosure_iff]
  refine ⟨fun τ => ⟨![τ 0 / r, 0], ?_⟩, ![1, 1], fun i => ?_, ?_⟩
  · funext i
    fin_cases i
    simp [Matrix.mulVec, dotProduct]
    field_simp
  · fin_cases i <;> simp
  · funext i
    fin_cases i
    simp [Matrix.mulVec, dotProduct]

end Examples
end RoboLean
