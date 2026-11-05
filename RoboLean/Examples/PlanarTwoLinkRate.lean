import RoboLean.Examples.PlanarTwoLinkControl

/-!
# The skewed energy of the planar two-link arm and its derivative in coordinates

MLS eqs. (4.10)–(4.11), printed p. 165, and the proof of Proposition 4.10, pp. 194–195, at a
constant set point with `K_p = K_v = I`.

For the arm of MLS Figure 4.4 (p. 164) the inertia matrix depends on the configuration only
through `c₂ = cos θ₂` and the Coriolis matrix only through `s₂ = sin θ₂` and the joint rate. With
`K_p = K_v = I` and `θ̇_d = 0` (so `θ̇ = ė`), the library's skewed energy and its derivative along
the closed loop are, with `e = (e₁, e₂)`, `ė = (ė₁, ė₂)` (indices `0, 1` in the code):

* `V = ½ ėᵀM(θ)ė + ½ (e₁² + e₂²) + ε eᵀM(θ)ė` (`planarTwoLinkModel_augmentedEnergy_one`);
* `V̇ = −|ė|² + ε ėᵀM(θ)ė − ε |e|² − ε eᵀė − ε β s₂ e₂ ė₁(ė₁ + ė₂)` with `β = m₂ l₁ r₂`
  (`planarTwoLinkModel_augmentedEnergyRate_one_one`).

The last term is the corrected cross term `ε eᵀ(Ṁ − C)ė = ε ėᵀ C e` of the library's reading of
p. 195: for this arm it is linear in the position error `e₂` and quadratic in the rate. The
quadratic form of the inertia matrix in coordinates is
`planarTwoLinkArm_dotProduct_massMatrix_mulVec`.

Conventions: `θ₂ = q 1` is the relative angle of the second joint; vectors in `Fin 2 → ℝ`; the
book's frame of Figure 4.4. Exact identities; no hypothesis on the parameters.
-/

noncomputable section

open Matrix

namespace RoboLean.Examples

variable (m₁ m₂ r₁ r₂ l₁ : ℝ) (I₁ I₂ : Fin 3 → ℝ)

/-- **The bilinear form of the planar arm's inertia matrix (MLS eq. (4.10), p. 165).** With
`α = I_z1 + I_z2 + m₁r₁² + m₂(l₁² + r₂²)`, `β = m₂l₁r₂`, `δ = I_z2 + m₂r₂²` and `c₂ = cos θ₂`:
`uᵀM(θ)v = (α + 2βc₂) u₁v₁ + (δ + βc₂)(u₁v₂ + u₂v₁) + δ u₂v₂` (indices `0, 1` in the code). -/
theorem planarTwoLinkArm_dotProduct_massMatrix_mulVec (q u v : Fin 2 → ℝ) :
    u ⬝ᵥ ((planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).massMatrix q *ᵥ v) =
      (I₁ 2 + I₂ 2 + m₁ * r₁ ^ 2 + m₂ * (l₁ ^ 2 + r₂ ^ 2) + 2 * (m₂ * l₁ * r₂) * Real.cos (q 1)) *
          (u 0 * v 0) +
        (I₂ 2 + m₂ * r₂ ^ 2 + m₂ * l₁ * r₂ * Real.cos (q 1)) * (u 0 * v 1 + u 1 * v 0) +
        (I₂ 2 + m₂ * r₂ ^ 2) * (u 1 * v 1) := by
  rw [planarTwoLinkArm_massMatrix]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
  ring

/-- **The skewed energy of the proof of MLS Proposition 4.10 (p. 194) for the planar arm with
`K_p = I`:** `V = ½ ėᵀM(θ)ė + ½(e₁² + e₂²) + ε eᵀM(θ)ė` at the configuration `q`, for any gravity
data and joint forces (MLS eq. (4.10), p. 165). -/
theorem planarTwoLinkModel_augmentedEnergy_one (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) (ε : ℝ) (q e w : Fin 2 → ℝ) :
    (planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).augmentedEnergy 1 ε q e w =
      1 / 2 * (w ⬝ᵥ ((planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).massMatrix q *ᵥ w)) +
        1 / 2 * (e 0 ^ 2 + e 1 ^ 2) +
        ε * (e ⬝ᵥ ((planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).massMatrix q *ᵥ w)) := by
  simp only [ManipulatorModel.augmentedEnergy, planarTwoLinkModel_M, Matrix.one_mulVec]
  rw [show e ⬝ᵥ e = e 0 ^ 2 + e 1 ^ 2 by simp [dotProduct, Fin.sum_univ_two, sq]]

/-- **The derivative of the skewed energy along the planar arm's closed loop at a constant set
point (MLS p. 195, corrected as in the library, with eq. (4.11), p. 165).** With `K_p = K_v = I`
and the joint rate equal to the velocity error `ė` (`θ̇_d = 0`):
`V̇ = −|ė|² + ε ėᵀM(θ)ė − ε|e|² − ε eᵀė − ε β (s₂ e₂) ė₁(ė₁ + ė₂)`, `β = m₂l₁r₂`, `s₂ = sin θ₂`
(Euclidean squares written out; indices `0, 1` in the code), for any gravity data and joint
forces. -/
theorem planarTwoLinkModel_augmentedEnergyRate_one_one (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) (ε : ℝ) (q e w : Fin 2 → ℝ) :
    (planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).augmentedEnergyRate 1 1 ε q w e w =
      -(w 0 ^ 2 + w 1 ^ 2) +
        ε * (w ⬝ᵥ ((planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).massMatrix q *ᵥ w)) -
        ε * (e 0 ^ 2 + e 1 ^ 2) - ε * (e 0 * w 0 + e 1 * w 1) -
        ε * (m₂ * l₁ * r₂) * (Real.sin (q 1) * e 1) * (w 0 * (w 0 + w 1)) := by
  set P := planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne with hP
  have hsymm : ∀ k, (P.chain.linkInertia k).IsSymm :=
    planarTwoLinkArm_linkInertia_isSymm m₁ m₂ r₁ r₂ l₁ I₁ I₂
  have hW : e ⬝ᵥ ((-1 + P.Mdot q w - P.C q w) *ᵥ w) = -(e ⬝ᵥ w) + w ⬝ᵥ (P.C q w *ᵥ e) := by
    rw [show -1 + P.Mdot q w - P.C q w = -1 + (P.Mdot q w - P.C q w) by abel,
      Matrix.add_mulVec, dotProduct_add, Matrix.neg_mulVec, dotProduct_neg, Matrix.one_mulVec,
      P.dotProduct_Mdot_sub_C_mulVec hsymm]
  simp only [ManipulatorModel.augmentedEnergyRate, Matrix.one_mulVec]
  rw [hW, hP, planarTwoLinkModel_C, planarTwoLinkModel_M]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
  ring

end RoboLean.Examples
