import Mathlib.LinearAlgebra.Trace
import RoboLean.Geometry.Reciprocal
import RoboLean.Geometry.TwistBracket
import RoboLean.Geometry.TwistScrew
import RoboLean.LieGroups.TwistForms

/-!
# The hyperbolic metric and the Killing form on `se(3)`

MLS Appendix A, §3.2, printed pp. 426–428: the two special cases of Proposition A.5.

* Example A.21, the hyperbolic metric `⟨ξ₁, ξ₂⟩_H = v₁ᵀ ω₂ + v₂ᵀ ω₁` (A.13), `β = 1, γ = 0`: its
  matrix squares to the identity with trace zero (eigenvalues `±1`, three of each), it takes
  negative values, it is nondegenerate, it scales linearly with a change of length scale, and it
  coincides with the reciprocal product of Chapter 2 (p. 67), which is therefore frame invariant
  (MLS Exercise 2.17(a), p. 78).
* Example A.22, the Killing form `⟨ξ₁, ξ₂⟩_K = -4 ω₁ᵀ ω₂` (A.14), `β = 0, γ = -4`: it equals
  `trace(ad_ξ₁ ∘ ad_ξ₂)` with `ad_ξ η = [ξ, η]` the twist bracket of Example A.8 (p. 411), it is
  degenerate, and it does not depend on the length scale.
* Example A.23, magnitude and pitch of a twist with `ω ≠ 0` through the two forms. Corrected
  printing: the display on p. 428 reads `M_ξ = -¼ ⟨ξ, ξ⟩_K`, but `-¼ ⟨ξ, ξ⟩_K = ‖ω‖²` while the
  magnitude of equation (2.44), p. 48, is `‖ω‖`; the statement proved is
  `M_ξ = √(-¼ ⟨ξ, ξ⟩_K)`, with `-¼ ⟨ξ, ξ⟩_K = M_ξ²` alongside. The pitch display
  `h_ξ = -2 ⟨ξ, ξ⟩_H / ⟨ξ, ξ⟩_K` is proved as printed.

A change of length scale by a factor `c` multiplies the linear coordinates of a twist by `c` and
leaves the angular coordinates unchanged (p. 426, "a change of length scale results in a linear
factor in the hyperbolic metric").
-/

noncomputable section

open Matrix

namespace RoboLean

namespace Twist

/-- The hyperbolic metric on `SE(3)` at the identity, MLS Example A.21, equation (A.13), printed
p. 426: the form of `[[0, I], [I, 0]]` (`β = 1, γ = 0` in Proposition A.5) on coordinates
`(v, ω)`. -/
def hyperbolicForm (ξ η : Twist) : ℝ := form (biInvariantMatrix 1 0) ξ η

/-- Equation (A.13), MLS printed p. 426: `⟨ξ₁, ξ₂⟩_H = v₁ᵀ ω₂ + v₂ᵀ ω₁`. -/
theorem hyperbolicForm_eq (ξ η : Twist) :
    hyperbolicForm ξ η = inner ℝ ξ.linear η.angular + inner ℝ η.linear ξ.angular := by
  rw [hyperbolicForm, form_biInvariantMatrix, real_inner_comm ξ.angular η.linear]
  ring

/-- MLS printed p. 426, "`⟨·, ·⟩_H` coincides with the reciprocal product defined in Chapter 2"
(the reciprocal product of p. 67). Coordinates `(v, ω)`. -/
theorem hyperbolicForm_eq_reciprocalProduct (ξ η : Twist) :
    hyperbolicForm ξ η = reciprocalProduct ξ η := by
  rw [hyperbolicForm_eq, reciprocalProduct_eq]

/-- The hyperbolic metric is invariant under change of coordinate frame, `⟨Ad_g ξ, Ad_g η⟩_H =
⟨ξ, η⟩_H` (MLS Example A.21 with Proposition A.5, printed pp. 425–426). -/
theorem hyperbolicForm_adjoint (g : RigidTransform) (ξ η : Twist) :
    hyperbolicForm (adjoint g ξ) (adjoint g η) = hyperbolicForm ξ η := by
  have h := (isAdInvariant_iff_eq_biInvariantMatrix (biInvariantMatrix 1 0)
    (biInvariantMatrix_transpose 1 0)).mpr ⟨1, 0, rfl⟩
  exact (isAdInvariant_iff_form _).mp h g ξ η

/-- MLS Exercise 2.17(a), printed p. 78: the reciprocal product of two screws is frame invariant,
`(Ad_g ξ) ⊙ (Ad_g η) = ξ ⊙ η` for every `g ∈ SE(3)`, proved through Example A.21 (p. 426).
Coordinates `(v, ω)`. -/
theorem reciprocalProduct_adjoint (g : RigidTransform) (ξ η : Twist) :
    reciprocalProduct (adjoint g ξ) (adjoint g η) = reciprocalProduct ξ η := by
  rw [← hyperbolicForm_eq_reciprocalProduct, ← hyperbolicForm_eq_reciprocalProduct,
    hyperbolicForm_adjoint]

/-- MLS printed p. 426, "the eigenvalues of the matrix representation of `⟨·, ·⟩_H` are all `±1`":
the matrix `[[0, I], [I, 0]]` squares to the identity. -/
theorem biInvariantMatrix_one_zero_mul_self :
    biInvariantMatrix 1 0 * biInvariantMatrix 1 0 = 1 := by
  rw [biInvariantMatrix, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  simp

/-- MLS printed p. 426, the eigenvalues of `⟨·, ·⟩_H` "occur pairwise": the matrix
`[[0, I], [I, 0]]` has trace zero, so with its square the identity the eigenvalues `1` and `-1`
each occur three times. -/
theorem trace_biInvariantMatrix_one_zero : (biInvariantMatrix 1 0).trace = 0 := by
  simp [biInvariantMatrix, Matrix.trace, Fintype.sum_sum_type]

/-- The eigenvectors of `[[0, I], [I, 0]]` for the eigenvalue `1` are the twists `(v, v)`
(MLS printed p. 426). -/
theorem biInvariantMatrix_one_zero_mulVec_self (v : Vec3) :
    biInvariantMatrix 1 0 *ᵥ (⟨v, v⟩ : Twist).coordinates = (⟨v, v⟩ : Twist).coordinates := by
  simp [biInvariantMatrix, coordinates, Matrix.fromBlocks_mulVec]

/-- The eigenvectors of `[[0, I], [I, 0]]` for the eigenvalue `-1` are the twists `(v, -v)`
(MLS printed p. 426). -/
theorem biInvariantMatrix_one_zero_mulVec_neg (v : Vec3) :
    biInvariantMatrix 1 0 *ᵥ (⟨v, -v⟩ : Twist).coordinates = -(⟨v, -v⟩ : Twist).coordinates := by
  ext i
  rcases i with i | i <;> simp [biInvariantMatrix, coordinates, Matrix.fromBlocks_mulVec]

/-- MLS printed p. 426, "it is possible for a vector to have negative 'length' with respect to the
hyperbolic metric": `⟨ξ, ξ⟩_H < 0` for `ξ = (e₁, -e₁)`. Coordinates `(v, ω)`. -/
theorem exists_hyperbolicForm_self_neg : ∃ ξ : Twist, hyperbolicForm ξ ξ < 0 := by
  refine ⟨⟨WithLp.toLp 2 ![1, 0, 0], -WithLp.toLp 2 ![1, 0, 0]⟩, ?_⟩
  rw [hyperbolicForm_eq]
  simp

/-- MLS printed p. 426, "the hyperbolic metric is nondegenerate": a twist `ξ` with
`⟨ξ, η⟩_H = 0` for every `η` is zero. -/
theorem hyperbolicForm_nondegenerate (ξ : Twist) (h : ∀ η : Twist, hyperbolicForm ξ η = 0) :
    ξ = 0 := by
  exact (reciprocalProduct_nondegenerate ξ).mp fun η => by
    rw [← hyperbolicForm_eq_reciprocalProduct]; exact h η

/-- A change of length scale by the factor `c`: the linear coordinates of a twist are multiplied
by `c`, the angular coordinates are unchanged (MLS printed pp. 426–428, the choice of length scale;
coordinates `(v, ω)`). -/
def scaleLength (c : ℝ) (ξ : Twist) : Twist := ⟨c • ξ.linear, ξ.angular⟩

/-- MLS printed p. 426, "a change of length scale results in a linear factor in the hyperbolic
metric": `⟨(c v₁, ω₁), (c v₂, ω₂)⟩_H = c ⟨ξ₁, ξ₂⟩_H`. -/
theorem hyperbolicForm_scaleLength (c : ℝ) (ξ η : Twist) :
    hyperbolicForm (scaleLength c ξ) (scaleLength c η) = c * hyperbolicForm ξ η := by
  simp only [hyperbolicForm_eq, scaleLength, inner_smul_left, conj_trivial]
  ring

/-- The Killing form on `SE(3)` at the identity, MLS Example A.22, equation (A.14), printed
p. 427: the form of `[[0, 0], [0, -4 I]]` (`β = 0, γ = -4` in Proposition A.5) on coordinates
`(v, ω)`. -/
def killingForm (ξ η : Twist) : ℝ := form (biInvariantMatrix 0 (-4)) ξ η

/-- Equation (A.14), MLS printed p. 427: `⟨ξ₁, ξ₂⟩_K = -4 ω₁ᵀ ω₂`. -/
theorem killingForm_eq (ξ η : Twist) :
    killingForm ξ η = -4 * inner ℝ ξ.angular η.angular := by
  rw [killingForm, form_biInvariantMatrix]
  ring

/-- MLS printed p. 427: the Killing form of (A.14) agrees with the general definition
`⟨ξ₁, ξ₂⟩_K = trace(ad_ξ₁ ∘ ad_ξ₂)`, `ad_ξ : η ↦ [ξ, η]`, the twist bracket of Example A.8
(p. 411), which is the matrix commutator of `ξ̂` and `η̂` (`Twist.hat_bracket`); "the factor of -4
… was chosen to make it agree with the general definition". Coordinates `(v, ω)`. -/
theorem killingForm_eq_trace (ξ η : Twist) :
    killingForm ξ η = LinearMap.trace ℝ Twist (bracketBilinear ξ ∘ₗ bracketBilinear η) := by
  have hl (x : Fin 3 ⊕ Fin 3 → ℝ) :
      (coordinatesEquiv.symm x).linear = WithLp.toLp 2 (fun i => x (Sum.inl i)) := rfl
  have ha (x : Fin 3 ⊕ Fin 3 → ℝ) :
      (coordinatesEquiv.symm x).angular = WithLp.toLp 2 (fun i => x (Sum.inr i)) := rfl
  rw [killingForm_eq, ← LinearMap.trace_conj' _ coordinatesEquiv,
    LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 3 ⊕ Fin 3)),
    LinearMap.toMatrix_eq_toMatrix']
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix'_apply, Fintype.sum_sum_type,
    Fin.sum_univ_three, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    coordinatesEquiv_apply]
  simp [coordinates, bracket, Vec3.cross, cross_apply, hl, ha, PiLp.inner_apply,
    Fin.sum_univ_three, Pi.single_apply]
  ring

/-- The Killing form is invariant under change of coordinate frame (MLS Example A.22 with
Proposition A.5, printed pp. 425–427). -/
theorem killingForm_adjoint (g : RigidTransform) (ξ η : Twist) :
    killingForm (adjoint g ξ) (adjoint g η) = killingForm ξ η := by
  have h := (isAdInvariant_iff_eq_biInvariantMatrix (biInvariantMatrix 0 (-4))
    (biInvariantMatrix_transpose 0 (-4))).mpr ⟨0, -4, rfl⟩
  exact (isAdInvariant_iff_form _).mp h g ξ η

/-- MLS printed p. 427, the Killing form "is degenerate": every pure translation `(v, 0)` is
orthogonal to every twist. -/
theorem killingForm_linear_left (v : Vec3) (η : Twist) : killingForm ⟨v, 0⟩ η = 0 := by
  simp [killingForm_eq]

/-- MLS printed p. 427, "the Killing form on `SE(3)` does not depend on the choice of length
scale". -/
theorem killingForm_scaleLength (c : ℝ) (ξ η : Twist) :
    killingForm (scaleLength c ξ) (scaleLength c η) = killingForm ξ η := by
  simp only [killingForm_eq, scaleLength]

/-- What the display of MLS Example A.23, printed p. 428, gives for the magnitude: for a twist
with `ω ≠ 0`, `-¼ ⟨ξ, ξ⟩_K = ‖ω‖² = M_ξ²`, the square of the magnitude of equation (2.44), p. 48.
-/
theorem neg_quarter_killingForm_self (ξ : Twist) (hω : ξ.angular ≠ 0) :
    -(1 / 4) * killingForm ξ ξ = screwMagnitude ξ ^ 2 := by
  rw [killingForm_eq, screwMagnitude_of_angular_ne_zero ξ hω, real_inner_self_eq_norm_sq]
  ring

/-- MLS Example A.23, printed p. 428, corrected printing: the magnitude of a twist with `ω ≠ 0`
(equation (2.44), p. 48) is `M_ξ = √(-¼ ⟨ξ, ξ⟩_K)`; the book prints the display without the
radical, which gives `M_ξ²`. -/
theorem screwMagnitude_eq_sqrt_killingForm (ξ : Twist) (hω : ξ.angular ≠ 0) :
    screwMagnitude ξ = √(-(1 / 4) * killingForm ξ ξ) := by
  rw [neg_quarter_killingForm_self ξ hω, Real.sqrt_sq (screwMagnitude_nonneg ξ)]

/-- MLS Example A.23, printed p. 428: the pitch of a twist with `ω ≠ 0` (equation (2.42), p. 47)
is `h_ξ = -2 ⟨ξ, ξ⟩_H / ⟨ξ, ξ⟩_K`. -/
theorem finitePitch_eq_hyperbolicForm_div_killingForm (ξ : Twist) (hω : ξ.angular ≠ 0) :
    finitePitch ξ hω = -2 * hyperbolicForm ξ ξ / killingForm ξ ξ := by
  have hn : ‖ξ.angular‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hω)
  rw [finitePitch, hyperbolicForm_eq, killingForm_eq, real_inner_self_eq_norm_sq,
    real_inner_comm ξ.linear ξ.angular]
  field_simp
  ring

/-- MLS printed p. 428, "the pitch of a screw obviously depends on the choice of length scale":
`h_{(c v, ω)} = c h_{(v, ω)}`. -/
theorem finitePitch_scaleLength (c : ℝ) (ξ : Twist) (hω : ξ.angular ≠ 0) :
    finitePitch (scaleLength c ξ) hω = c * finitePitch ξ hω := by
  simp only [finitePitch, scaleLength, inner_smul_right]
  ring

end Twist

end RoboLean
