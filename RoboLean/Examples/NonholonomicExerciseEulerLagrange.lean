import RoboLean.Examples.NonholonomicBrockett
import RoboLean.Nonholonomic.OptimalInputs

/-!
# The Euler–Lagrange equations of the `m`-input system (8.5): MLS Chapter 8, Exercise 3(a)

MLS Chapter 8, Exercise 3, printed pp. 391–392: for `q̇ = u`, `Ẏ = quᵀ − uqᵀ`, `u ∈ ℝᵐ`,
`Y ∈ so(m)`, "(a) Derive the Euler-Lagrange equations for the system, by minimizing the following
integral `½ ∫₀¹ uᵀu dt`"; (b) the optimal inputs for `q(0) = q(1) = 0`, `Y(0) = 0`, `Y(1) = ŷ`,
`y ∈ ℝ³`; (c) the input steering `(0, 0)` to `(0, Ỹ)`.

**What is formalized.** Part (a) by the method of Proposition 8.4 (p. 373), with the necessary
conditions (8.12)–(8.13) as hypotheses along a curve `(z, p)` on `[0, T]`, `z = (q, Y)` on the
library's state space `ℝᵐ × ℝ^{m×m}` of (8.4)–(8.5):
* the brackets are constant, `[gᵢ, gⱼ] = (0, 2(Eᵢⱼ − Eⱼᵢ))`: the `Y`-entry `(a, b)` of
  `[gᵢ, gⱼ]` is `2(δᵢₐδⱼ_b − δⱼₐδᵢ_b)`;
* the `Y`-part of the multiplier is constant, since the fields do not depend on `Y`;
* hence the Euler–Lagrange equations are `u̇ = Λu` with the constant `Λ ∈ so(m)`,
  `Λᵢⱼ = 2(Pᵢⱼ − Pⱼᵢ)`, `Pₐ_b = p(0)(0, E_{ab})` (equivalently `q̈ = Λq̇`), the `m`-input form of
  (8.3), p. 359.
Parts (b) and (c) are not formalized: (b) needs the solution of `u̇ = Λu` in `SO(3)` with the
boundary conditions, and (c) needs a concatenation or several frequencies (Algorithm 1, p. 361;
one pair step is the library's `IsTrajectory.brockettSystem_steering`).
-/

noncomputable section

open Set VectorField Matrix

namespace RoboLean
namespace Examples

open RoboLean.Nonholonomic

variable {m : ℕ}

/-- The linear part of `gⱼ` (supporting definition for MLS p. 360). -/
private def brockettLin (j : Fin m) :
    ((Fin m → ℝ) × (Fin m → Fin m → ℝ)) →L[ℝ] ((Fin m → ℝ) × (Fin m → Fin m → ℝ)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => (0, fun a b =>
        z.1 a * (Pi.single j (1 : ℝ) : Fin m → ℝ) b - (Pi.single j (1 : ℝ) : Fin m → ℝ) a * z.1 b)
      map_add' := by
        intro z w
        ext a b
        · simp
        · simp
          ring
      map_smul' := by
        intro c z
        ext a b
        · simp
        · simp
          ring }

private theorem brockettLin_apply (j : Fin m) (z : (Fin m → ℝ) × (Fin m → Fin m → ℝ)) :
    brockettLin j z = (0, fun a b =>
      z.1 a * (Pi.single j (1 : ℝ) : Fin m → ℝ) b - (Pi.single j (1 : ℝ) : Fin m → ℝ) a * z.1 b) :=
  rfl

private theorem hasFDerivAt_brockettSystemFields (j : Fin m)
    (z : (Fin m → ℝ) × (Fin m → Fin m → ℝ)) :
    HasFDerivAt (brockettSystemFields m j) (brockettLin j) z := by
  have h := (brockettLin j).hasFDerivAt (x := z) |>.const_add
    ((Pi.single j 1 : Fin m → ℝ), (0 : Fin m → Fin m → ℝ))
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
  ext a b
  · simp [brockettSystemFields, brockettLin_apply]
  · simp [brockettSystemFields, brockettLin_apply]

/-- **MLS Chapter 8, Exercise 3(a), pp. 391–392, for (8.5), p. 360: the brackets are constant,**
the `Y`-entry `(a, b)` of `[gᵢ, gⱼ]` is `2(δᵢₐδⱼ_b − δⱼₐδᵢ_b)` and the `q`-part is zero. -/
theorem brockettSystem_lieBracket (i j : Fin m) (z : (Fin m → ℝ) × (Fin m → Fin m → ℝ)) :
    lieBracket ℝ (brockettSystemFields m i) (brockettSystemFields m j) z =
      (0, fun a b => 2 * ((Pi.single i (1 : ℝ) : Fin m → ℝ) a * (Pi.single j (1 : ℝ) : Fin m → ℝ) b -
        (Pi.single j (1 : ℝ) : Fin m → ℝ) a * (Pi.single i (1 : ℝ) : Fin m → ℝ) b)) := by
  rw [lieBracket_eq]
  show fderiv ℝ (brockettSystemFields m j) z (brockettSystemFields m i z) -
    fderiv ℝ (brockettSystemFields m i) z (brockettSystemFields m j z) = _
  rw [(hasFDerivAt_brockettSystemFields j z).fderiv, (hasFDerivAt_brockettSystemFields i z).fderiv,
    brockettLin_apply, brockettLin_apply]
  ext a b
  · simp [brockettSystemFields]
  · simp [brockettSystemFields]
    ring

/-- **MLS Chapter 8, Exercise 3(a), pp. 391–392: the `Y`-part of the multiplier is constant**
along a curve satisfying (8.12) for (8.5): `p(t)(0, W) = p(0)(0, W)` on `[0, T]`. -/
theorem brockettSystem_multiplier_const {z : ℝ → (Fin m → ℝ) × (Fin m → Fin m → ℝ)}
    {p : ℝ → ((Fin m → ℝ) × (Fin m → Fin m → ℝ)) →L[ℝ] ℝ} {T : ℝ}
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p (-∑ i, optimalInput (brockettSystemFields m) z p t i •
      (p t).comp (fderiv ℝ (brockettSystemFields m i) (z t))) t)
    (W : Fin m → Fin m → ℝ) :
    ∀ t ∈ Icc 0 T, p t (0, W) = p 0 (0, W) := by
  have hd : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => p s (0, W)) 0 t := by
    intro t ht
    have h := (hp t ht).clm_apply (hasDerivAt_const t ((0 : Fin m → ℝ), W))
    convert h using 1
    have hz : ∀ i, fderiv ℝ (brockettSystemFields m i) (z t) ((0 : Fin m → ℝ), W) = 0 := by
      intro i
      rw [(hasFDerivAt_brockettSystemFields i (z t)).fderiv, brockettLin_apply]
      ext a b <;> simp
    simp [hz]
  intro t ht
  refine constant_of_has_deriv_right_zero (f := fun s => p s (0, W)) ?_ ?_ t ht
  · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
  · exact fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt

/-- **MLS Chapter 8, Exercise 3(a), pp. 391–392: the constant matrix `Λ`,**
`Λᵢⱼ = 2(Pᵢⱼ − Pⱼᵢ)` with `Pₐ_b = p(0, E_{ab})`. -/
def brockettSystemLambda (p : ((Fin m → ℝ) × (Fin m → Fin m → ℝ)) →L[ℝ] ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => 2 * (p (0, fun a b => (Pi.single i (1 : ℝ) : Fin m → ℝ) a *
      (Pi.single j (1 : ℝ) : Fin m → ℝ) b) -
    p (0, fun a b => (Pi.single j (1 : ℝ) : Fin m → ℝ) a * (Pi.single i (1 : ℝ) : Fin m → ℝ) b))

/-- **MLS Chapter 8, Exercise 3(a), pp. 391–392: `Λ ∈ so(m)`.** -/
theorem brockettSystemLambda_transpose (p : ((Fin m → ℝ) × (Fin m → Fin m → ℝ)) →L[ℝ] ℝ) :
    (brockettSystemLambda p)ᵀ = -brockettSystemLambda p := by
  ext i j
  simp [brockettSystemLambda]
  ring

/-- **MLS Chapter 8, Exercise 3(a), pp. 391–392: the Euler–Lagrange equations of (8.5),**
`u̇ = Λu` on `[0, T]` with the constant `Λ = brockettSystemLambda (p 0) ∈ so(m)`, along a curve
satisfying the necessary conditions (8.12)–(8.13): `Ω(z(t), p(t)) = Λ` for all `t ∈ [0, T]`. -/
theorem brockettSystem_eulerLagrange {z : ℝ → (Fin m → ℝ) × (Fin m → Fin m → ℝ)}
    {p : ℝ → ((Fin m → ℝ) × (Fin m → Fin m → ℝ)) →L[ℝ] ℝ} {T : ℝ}
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z
      (driftFree (brockettSystemFields m) (z t) (optimalInput (brockettSystemFields m) z p t)) t)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p (-∑ i, optimalInput (brockettSystemFields m) z p t i •
      (p t).comp (fderiv ℝ (brockettSystemFields m i) (z t))) t) :
    (∀ t ∈ Icc 0 T, optimalOmega (brockettSystemFields m) (z t) (p t) = brockettSystemLambda (p 0)) ∧
      ∀ t ∈ Icc 0 T, HasDerivAt (optimalInput (brockettSystemFields m) z p)
        (brockettSystemLambda (p 0) *ᵥ optimalInput (brockettSystemFields m) z p t) t := by
  have hΩ : ∀ t ∈ Icc 0 T, optimalOmega (brockettSystemFields m) (z t) (p t) =
      brockettSystemLambda (p 0) := by
    intro t ht
    ext i j
    simp only [optimalOmega, Matrix.of_apply, brockettSystemLambda, brockettSystem_lieBracket]
    have hsplit : ((0 : Fin m → ℝ), fun a b => 2 * ((Pi.single i (1 : ℝ) : Fin m → ℝ) a *
        (Pi.single j (1 : ℝ) : Fin m → ℝ) b - (Pi.single j (1 : ℝ) : Fin m → ℝ) a *
        (Pi.single i (1 : ℝ) : Fin m → ℝ) b)) =
        (2 : ℝ) • (((0 : Fin m → ℝ), fun a b => (Pi.single i (1 : ℝ) : Fin m → ℝ) a *
          (Pi.single j (1 : ℝ) : Fin m → ℝ) b) - ((0 : Fin m → ℝ), fun a b =>
          (Pi.single j (1 : ℝ) : Fin m → ℝ) a * (Pi.single i (1 : ℝ) : Fin m → ℝ) b)) := by
      ext a b
      · simp
      · simp
    rw [hsplit, map_smul, map_sub, brockettSystem_multiplier_const hp _ t ht,
      brockettSystem_multiplier_const hp _ t ht, smul_eq_mul]
  refine ⟨hΩ, fun t ht => ?_⟩
  rw [← hΩ t ht]
  exact hasDerivAt_optimalInput
    (fun i s _ => (hasFDerivAt_brockettSystemFields i (z s)).differentiableAt) hz hp t ht

end Examples
end RoboLean
