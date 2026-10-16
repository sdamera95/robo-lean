import RoboLean.Control.MatrixAnalysis
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Kinematics of planar contact (MLS Exercise 17(a))

MLS Chapter 5, Exercise 17, printed pp. 262–263: "The kinematics of contact for two planar objects
can be obtained by restricting equation (5.28) to the plane. Let `g_of = (p, R) ∈ SE(2)` be the
relative configuration of the objects. (a) Let `s_o ∈ ℝ` be the point of contact on the object and
`s_f ∈ ℝ` be the point of contact on the finger. Assume that the surface is parameterized by arc
length, so that `‖∂cᵢ/∂sᵢ‖ = 1` where `cᵢ : ℝ → ℝ²` is a coordinate chart. Show that the contact
coordinates `η = (s_f, s_o)` evolve according to
`ṡ_f = (K_o + K_f)⁻¹ ((∂c_o/∂s_o)ᵀ Ṙ n_f + K_o (∂c_o/∂s_o)ᵀ (Ṙ c_f + ṗ))`,
`ṡ_o = (K_o + K_f)⁻¹ (−(∂c_o/∂s_o)ᵀ Ṙ n_f + K_f (∂c_o/∂s_o)ᵀ (Ṙ c_f + ṗ))`."

**Conventions fixed here (the exercise leaves `n_f` and `Kᵢ` undefined).** Points and vectors of the
plane are `Fin 2 → ℝ` with the dot product `⬝ᵥ`; `R` is a matrix curve with `R(t) ∈ SO(2)`
(Mathlib's `specialOrthogonalGroup (Fin 2) ℝ`), and `g_of = (p, R)` maps finger coordinates to
object coordinates (`x ↦ p + R x`). A chart `cᵢ` has unit tangent `tᵢ = cᵢ'`, normal `nᵢ = J tᵢ`
with `J = [[0, −1], [1, 0]]` the rotation by `+π/2`, and curvature `Kᵢ` defined by `nᵢ' = Kᵢ tᵢ`
(the planar form of MLS eq. (5.23), p. 245, `K = xᵀ n_u / ‖c_u‖` with `x = t` and `‖c_u‖ = 1`). The
two curves are in contact when `c_o(s_o) = p + R c_f(s_f)` and their normals are opposed,
`n_o(s_o) = −R n_f(s_f)` (the planar form of the third column `−1` of the contact rotation
`diag(R_ψ, −1)` of MLS eq. (5.34), p. 251). Sliding is allowed: the result holds for every
differentiable motion that keeps the curves in contact.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Grasp

/-- **The rotation by `+π/2` of the plane, `J = [[0, −1], [1, 0]]`**, giving the normal `n = J t` of
a planar curve with unit tangent `t` (convention fixed here for MLS Exercise 17, printed p. 262,
which leaves `n_f` undefined). -/
def planarNormalRotation : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- **A planar chart parameterized by arc length with its tangent and curvature (MLS Exercise 17(a),
printed p. 262):** `c : ℝ → ℝ²` has the derivative `t(s)` at every `s`, `‖t(s)‖ = 1` ("parameterized
by arc length, so that `‖∂cᵢ/∂sᵢ‖ = 1`"), and the normal `n = J t` has the derivative `K(s) t(s)`,
which defines the curvature `K` (the planar form of MLS eq. (5.23), p. 245). -/
structure IsUnitSpeedCurve (c t : ℝ → Fin 2 → ℝ) (K : ℝ → ℝ) : Prop where
  /-- The tangent `t = c'` (MLS Exercise 17(a), p. 262). -/
  hasDerivAt : ∀ s, HasDerivAt c (t s) s
  /-- Arc-length parameterization, `‖∂c/∂s‖ = 1` (MLS Exercise 17(a), p. 262). -/
  unit : ∀ s, t s ⬝ᵥ t s = 1
  /-- The normal `n = J t` has the derivative `K t` (planar form of MLS eq. (5.23), p. 245). -/
  hasDerivAt_normal : ∀ s, HasDerivAt (fun s => planarNormalRotation *ᵥ t s) (K s • t s) s

variable {co cf tO tF : ℝ → Fin 2 → ℝ} {Ko Kf : ℝ → ℝ}

/-- **The planar contact constraints (MLS Exercise 17(a), printed pp. 262–263, the planar
restriction of eq. (5.37), p. 252):** along a differentiable relative motion `g_of = (p, R)` that
keeps the two curves in contact with opposed normals near `t`, with contact coordinates
`(s_f, s_o)`, `ṡ_o + ṡ_f = t_oᵀ (Ṙ c_f + ṗ)` and `K_o ṡ_o − K_f ṡ_f = −t_oᵀ Ṙ n_f`, every quantity
at the contact point at time `t`. -/
theorem planarContact_constraints (ho : IsUnitSpeedCurve co tO Ko)
    (hf : IsUnitSpeedCurve cf tF Kf) {p : ℝ → Fin 2 → ℝ} {R : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {so sf : ℝ → ℝ} {p' : Fin 2 → ℝ} {R' : Matrix (Fin 2) (Fin 2) ℝ} {so' sf' t : ℝ}
    (hR : R t ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) (hp : HasDerivAt p p' t)
    (hRd : HasDerivAt R R' t) (hso : HasDerivAt so so' t) (hsf : HasDerivAt sf sf' t)
    (hc : ∀ᶠ s in 𝓝 t, co (so s) = p s + R s *ᵥ cf (sf s))
    (hn : ∀ᶠ s in 𝓝 t, planarNormalRotation *ᵥ tO (so s) =
      -(R s *ᵥ (planarNormalRotation *ᵥ tF (sf s)))) :
    so' + sf' = tO (so t) ⬝ᵥ (R' *ᵥ cf (sf t) + p') ∧
      Ko (so t) * so' - Kf (sf t) * sf' =
        -(tO (so t) ⬝ᵥ (R' *ᵥ (planarNormalRotation *ᵥ tF (sf t)))) := by
  have hR' := Control.hasDerivAt_matrix_iff.mp hRd
  have h1 : HasDerivAt (fun s => co (so s)) (so' • tO (so t)) t :=
    (ho.hasDerivAt (so t)).scomp t hso
  have h2 := (hp.add (Control.hasDerivAt_matrix_mulVec hR'
    ((hf.hasDerivAt (sf t)).scomp t hsf))).congr_of_eventuallyEq hc
  have E1 := h1.unique h2
  have h3 : HasDerivAt (fun s => planarNormalRotation *ᵥ tO (so s))
      (so' • (Ko (so t) • tO (so t))) t := (ho.hasDerivAt_normal (so t)).scomp t hso
  have h4 := (Control.hasDerivAt_matrix_mulVec hR'
    ((hf.hasDerivAt_normal (sf t)).scomp t hsf)).neg.congr_of_eventuallyEq hn
  have E2 := h3.unique h4
  have N := hn.self_of_nhds
  obtain ⟨ha, hb, -⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp hR
  have U := ho.unit (so t)
  have E10 := congrFun E1 0
  have E11 := congrFun E1 1
  have E20 := congrFun E2 0
  have E21 := congrFun E2 1
  have N0 := congrFun N 0
  have N1 := congrFun N 1
  simp [planarNormalRotation, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] at E10 E11 E20 E21 N0 N1 U ⊢
  simp only [ha, hb] at E10 E11 E20 E21 N0 N1
  refine ⟨?_, ?_⟩
  · linear_combination tO (so t) 0 * E10 + tO (so t) 1 * E11 - (so' + sf') * U +
      sf' * tO (so t) 0 * N1 - sf' * tO (so t) 1 * N0
  · linear_combination tO (so t) 0 * E20 + tO (so t) 1 * E21 - Ko (so t) * so' * U +
      Kf (sf t) * sf' * U - Kf (sf t) * sf' * tO (so t) 0 * N1 +
      Kf (sf t) * sf' * tO (so t) 1 * N0

/-- **MLS Exercise 17(a), printed pp. 262–263: the kinematics of planar contact.** Along a
differentiable relative motion `g_of = (p, R) ∈ SE(2)` that keeps the two arc-length curves in
contact with opposed normals near `t`, if `K_o + K_f ≠ 0` at the contact point, the contact
coordinates `η = (s_f, s_o)` evolve according to
`ṡ_f = (K_o + K_f)⁻¹ (t_oᵀ Ṙ n_f + K_o t_oᵀ (Ṙ c_f + ṗ))` and
`ṡ_o = (K_o + K_f)⁻¹ (−t_oᵀ Ṙ n_f + K_f t_oᵀ (Ṙ c_f + ṗ))`, with `t_o = ∂c_o/∂s_o`, `n_f = J t_f`
and every quantity at the contact point at time `t`. -/
theorem planarContact_kinematics (ho : IsUnitSpeedCurve co tO Ko)
    (hf : IsUnitSpeedCurve cf tF Kf) {p : ℝ → Fin 2 → ℝ} {R : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {so sf : ℝ → ℝ} {p' : Fin 2 → ℝ} {R' : Matrix (Fin 2) (Fin 2) ℝ} {so' sf' t : ℝ}
    (hR : R t ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) (hp : HasDerivAt p p' t)
    (hRd : HasDerivAt R R' t) (hso : HasDerivAt so so' t) (hsf : HasDerivAt sf sf' t)
    (hc : ∀ᶠ s in 𝓝 t, co (so s) = p s + R s *ᵥ cf (sf s))
    (hn : ∀ᶠ s in 𝓝 t, planarNormalRotation *ᵥ tO (so s) =
      -(R s *ᵥ (planarNormalRotation *ᵥ tF (sf s))))
    (hK : Ko (so t) + Kf (sf t) ≠ 0) :
    sf' = (Ko (so t) + Kf (sf t))⁻¹ *
        (tO (so t) ⬝ᵥ (R' *ᵥ (planarNormalRotation *ᵥ tF (sf t))) +
          Ko (so t) * (tO (so t) ⬝ᵥ (R' *ᵥ cf (sf t) + p'))) ∧
      so' = (Ko (so t) + Kf (sf t))⁻¹ *
        (-(tO (so t) ⬝ᵥ (R' *ᵥ (planarNormalRotation *ᵥ tF (sf t)))) +
          Kf (sf t) * (tO (so t) ⬝ᵥ (R' *ᵥ cf (sf t) + p'))) := by
  obtain ⟨hA, hB⟩ := planarContact_constraints ho hf hR hp hRd hso hsf hc hn
  refine ⟨(eq_inv_mul_iff_mul_eq₀ hK).mpr ?_, (eq_inv_mul_iff_mul_eq₀ hK).mpr ?_⟩
  · linear_combination Ko (so t) * hA - hB
  · linear_combination Kf (sf t) * hA + hB

end Grasp
end RoboLean
