import RoboLean.Grasp.PlanarContactKinematics

/-!
# Kinematics of planar contact for curves of any speed (MLS Exercise 17)

MLS Chapter 5, Exercise 17, printed pp. 262–263. Part (a) assumes that both curves are parameterized
by arc length (`‖∂cᵢ/∂sᵢ‖ = 1`) and is `Grasp.planarContact_kinematics`. Part (b), "Derive the
equations of contact for a planar, elliptical finger rolling against a flat object", needs a chart
of an ellipse, and the arc length of an ellipse is not an elementary function of the usual angle
parameter. This file states the kinematics of (a) for regular charts of any speed, as MLS
eq. (5.28), p. 250, does for surfaces through the metric tensor `M`.

**Conventions (those of `Grasp.PlanarContactKinematics`, with a speed).** A chart `c` has derivative
`c' = σ t` with `σ` its speed and `t` a unit tangent, normal `n = J t` with `J` the rotation by
`+π/2`, and curvature `K` (with respect to arc length) defined by `n' = σ K t`, the planar form of
MLS eq. (5.23), p. 245, `K = xᵀ n_u/‖c_u‖`. The curves are in contact when
`c_o(s_o) = p + R c_f(s_f)` with opposed normals `n_o = −R n_f`. With `σ ≡ 1` this is Exercise 17(a)
(`IsUnitSpeedCurve.isRegularCurve`). The result holds for sliding as well as rolling motions.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Grasp

/-- **A regular planar chart with its speed, unit tangent and curvature (MLS Exercise 17, printed
p. 262, without the arc-length assumption):** `c` has the derivative `σ(s) t(s)` at every `s`, the
tangent `t` is a unit vector, and the normal `n = J t` has the derivative `σ(s) K(s) t(s)`, which
defines the curvature `K` with respect to arc length (the planar form of MLS eq. (5.23), p. 245). -/
structure IsRegularCurve (c t : ℝ → Fin 2 → ℝ) (σ K : ℝ → ℝ) : Prop where
  /-- The derivative `c' = σ t` (MLS Exercise 17, p. 262; `σ` is the speed `‖∂c/∂s‖`). -/
  hasDerivAt : ∀ s, HasDerivAt c (σ s • t s) s
  /-- The tangent `t` is a unit vector (MLS Exercise 17, p. 262). -/
  unit : ∀ s, t s ⬝ᵥ t s = 1
  /-- The normal `n = J t` has the derivative `σ K t` (planar form of MLS eq. (5.23), p. 245). -/
  hasDerivAt_normal : ∀ s,
    HasDerivAt (fun s => planarNormalRotation *ᵥ t s) ((σ s * K s) • t s) s

variable {c t co cf tO tF : ℝ → Fin 2 → ℝ} {K Ko Kf σo σf : ℝ → ℝ}

/-- **An arc-length chart is a regular chart of speed `1` (MLS Exercise 17(a), printed p. 262,
"parameterized by arc length, so that `‖∂cᵢ/∂sᵢ‖ = 1`").** -/
theorem IsUnitSpeedCurve.isRegularCurve (h : IsUnitSpeedCurve c t K) :
    IsRegularCurve c t (fun _ => 1) K where
  hasDerivAt s := by simpa using h.hasDerivAt s
  unit := h.unit
  hasDerivAt_normal s := by simpa using h.hasDerivAt_normal s

/-- **The planar contact constraints for regular charts (MLS Exercise 17, printed pp. 262–263, the
planar restriction of eq. (5.37), p. 252):** along a differentiable relative motion
`g_of = (p, R)` that keeps the two curves in contact with opposed normals near `t`, with contact
coordinates `(s_f, s_o)`, `σ_o ṡ_o + σ_f ṡ_f = t_oᵀ (Ṙ c_f + ṗ)` and
`K_o σ_o ṡ_o − K_f σ_f ṡ_f = −t_oᵀ Ṙ n_f`, every quantity at the contact point at time `t`. -/
theorem planarRegularContact_constraints (ho : IsRegularCurve co tO σo Ko)
    (hf : IsRegularCurve cf tF σf Kf) {p : ℝ → Fin 2 → ℝ} {R : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {so sf : ℝ → ℝ} {p' : Fin 2 → ℝ} {R' : Matrix (Fin 2) (Fin 2) ℝ} {so' sf' t : ℝ}
    (hR : R t ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) (hp : HasDerivAt p p' t)
    (hRd : HasDerivAt R R' t) (hso : HasDerivAt so so' t) (hsf : HasDerivAt sf sf' t)
    (hc : ∀ᶠ s in 𝓝 t, co (so s) = p s + R s *ᵥ cf (sf s))
    (hn : ∀ᶠ s in 𝓝 t, planarNormalRotation *ᵥ tO (so s) =
      -(R s *ᵥ (planarNormalRotation *ᵥ tF (sf s)))) :
    σo (so t) * so' + σf (sf t) * sf' = tO (so t) ⬝ᵥ (R' *ᵥ cf (sf t) + p') ∧
      Ko (so t) * (σo (so t) * so') - Kf (sf t) * (σf (sf t) * sf') =
        -(tO (so t) ⬝ᵥ (R' *ᵥ (planarNormalRotation *ᵥ tF (sf t)))) := by
  have hR' := Control.hasDerivAt_matrix_iff.mp hRd
  have h1 : HasDerivAt (fun s => co (so s)) (so' • (σo (so t) • tO (so t))) t :=
    (ho.hasDerivAt (so t)).scomp t hso
  have h2 := (hp.add (Control.hasDerivAt_matrix_mulVec hR'
    ((hf.hasDerivAt (sf t)).scomp t hsf))).congr_of_eventuallyEq hc
  have E1 := h1.unique h2
  have h3 : HasDerivAt (fun s => planarNormalRotation *ᵥ tO (so s))
      (so' • ((σo (so t) * Ko (so t)) • tO (so t))) t :=
    (ho.hasDerivAt_normal (so t)).scomp t hso
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
  set vo := σo (so t) * so'
  set vf := σf (sf t) * sf'
  refine ⟨?_, ?_⟩
  · linear_combination tO (so t) 0 * E10 + tO (so t) 1 * E11 - (vo + vf) * U +
      vf * tO (so t) 0 * N1 - vf * tO (so t) 1 * N0
  · linear_combination tO (so t) 0 * E20 + tO (so t) 1 * E21 - Ko (so t) * vo * U +
      Kf (sf t) * vf * U - Kf (sf t) * vf * tO (so t) 0 * N1 +
      Kf (sf t) * vf * tO (so t) 1 * N0

/-- **The kinematics of planar contact for regular charts (MLS Exercise 17, printed pp. 262–263):**
under the hypotheses of `planarRegularContact_constraints`, if `K_o + K_f ≠ 0` at the contact point,
`σ_f ṡ_f = (K_o + K_f)⁻¹ (t_oᵀ Ṙ n_f + K_o t_oᵀ (Ṙ c_f + ṗ))` and
`σ_o ṡ_o = (K_o + K_f)⁻¹ (−t_oᵀ Ṙ n_f + K_f t_oᵀ (Ṙ c_f + ṗ))`; with `σ ≡ 1` these are the formulas
of Exercise 17(a). -/
theorem planarRegularContact_kinematics (ho : IsRegularCurve co tO σo Ko)
    (hf : IsRegularCurve cf tF σf Kf) {p : ℝ → Fin 2 → ℝ} {R : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {so sf : ℝ → ℝ} {p' : Fin 2 → ℝ} {R' : Matrix (Fin 2) (Fin 2) ℝ} {so' sf' t : ℝ}
    (hR : R t ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) (hp : HasDerivAt p p' t)
    (hRd : HasDerivAt R R' t) (hso : HasDerivAt so so' t) (hsf : HasDerivAt sf sf' t)
    (hc : ∀ᶠ s in 𝓝 t, co (so s) = p s + R s *ᵥ cf (sf s))
    (hn : ∀ᶠ s in 𝓝 t, planarNormalRotation *ᵥ tO (so s) =
      -(R s *ᵥ (planarNormalRotation *ᵥ tF (sf s))))
    (hK : Ko (so t) + Kf (sf t) ≠ 0) :
    σf (sf t) * sf' = (Ko (so t) + Kf (sf t))⁻¹ *
        (tO (so t) ⬝ᵥ (R' *ᵥ (planarNormalRotation *ᵥ tF (sf t))) +
          Ko (so t) * (tO (so t) ⬝ᵥ (R' *ᵥ cf (sf t) + p'))) ∧
      σo (so t) * so' = (Ko (so t) + Kf (sf t))⁻¹ *
        (-(tO (so t) ⬝ᵥ (R' *ᵥ (planarNormalRotation *ᵥ tF (sf t)))) +
          Kf (sf t) * (tO (so t) ⬝ᵥ (R' *ᵥ cf (sf t) + p'))) := by
  obtain ⟨hA, hB⟩ := planarRegularContact_constraints ho hf hR hp hRd hso hsf hc hn
  refine ⟨(eq_inv_mul_iff_mul_eq₀ hK).mpr ?_, (eq_inv_mul_iff_mul_eq₀ hK).mpr ?_⟩
  · linear_combination Ko (so t) * hA - hB
  · linear_combination Kf (sf t) * hA + hB

end Grasp
end RoboLean
