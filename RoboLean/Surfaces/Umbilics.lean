import RoboLean.Surfaces.LinesOfCurvature
import RoboLean.Surfaces.LevelSet

/-!
# Umbilics from a normal field (MLS eq. (5.21), p. 245, and Exercise 19, p. 263)

MLS p. 245 defines the curvature tensor (5.21) of a chart, `K = [x y]ᵀ [n_u/‖c_u‖ n_v/‖c_v‖]`; for
a surface given by a normal field `G` (a level set, Exercise 19, p. 263) the library computes it from
`DG` (`curvatureTensor_eq_of_gaussNormal`). An umbilic of a chart is a point where `K` is a multiple
of the identity (`IsUmbilicAt`; the book does not use the word).

**Proved here.** If at the surface point `p = c(α)` the bilinear form `(w, w') ↦ wᵀ DG(p) w'` on the
plane orthogonal to `G(p)` is `κ` times the inner product, then every chart `c` through `p` that is
differentiable at `α`, orthogonal at `α` with `c_u, c_v ≠ 0`, and has Gauss normal `G/‖G‖` near
`α` has `K(α) = (κ/‖G(p)‖) I`, so `α` is an umbilic of `c` (`curvatureTensor_eq_smul_one_of_form`,
`isUmbilicAt_of_form`). The condition is on the surface and its normal field alone, so it gives the
same umbilic for every such chart.

**Conventions.** `normalizedField`, `curvatureTensor`, `IsOrthogonalAt` and `IsUmbilicAt` as in the
library's Chapter 5 modules; inner products are Mathlib's `inner ℝ`.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Surface

variable {c : (Fin 2 → ℝ) → Vec3} {α : Fin 2 → ℝ}

/-- **The curvature tensor at a point where the normal field's derivative is a multiple of the
identity on the tangent plane (MLS eq. (5.21), p. 245, with Exercise 19, p. 263):** if `c` is
differentiable at `α`, orthogonal at `α` with `c_u, c_v ≠ 0`, its Gauss normal is `G/‖G‖` along `c`
near `α`, `G` is differentiable at `c(α)` with `G(c(α)) ≠ 0`, and `wᵀ DG w' = κ wᵀ w'` for all `w, w'`
orthogonal to `G(c(α))`, then `K(α) = (κ/‖G(c(α))‖) I`. -/
theorem curvatureTensor_eq_smul_one_of_form {G : Vec3 → Vec3} (hc : DifferentiableAt ℝ c α)
    (hG : DifferentiableAt ℝ G (c α)) (h0 : G (c α) ≠ 0)
    (hn : gaussNormal c =ᶠ[𝓝 α] fun β => normalizedField G (c β)) (horth : IsOrthogonalAt c α)
    (hu : partialU c α ≠ 0) (hv : partialV c α ≠ 0) {κ : ℝ}
    (hκ : ∀ w w' : Vec3, inner ℝ w (G (c α)) = 0 → inner ℝ w' (G (c α)) = 0 →
      inner ℝ w (fderiv ℝ G (c α) w') = κ * inner ℝ w w') :
    curvatureTensor c α = (κ / ‖G (c α)‖) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨ou, ov⟩ := inner_partial_field_eq_zero h0 hn.self_of_nhds
  have hvu : inner ℝ (partialV c α) (partialU c α) = 0 := by
    rw [real_inner_comm]; exact horth
  have hu2 : ‖partialU c α‖ ≠ 0 := norm_ne_zero_iff.2 hu
  have hv2 : ‖partialV c α‖ ≠ 0 := norm_ne_zero_iff.2 hv
  have hG2 : ‖G (c α)‖ ≠ 0 := norm_ne_zero_iff.2 h0
  rw [curvatureTensor_eq_of_gaussNormal hc hG h0 hn, hκ _ _ ou ou, hκ _ _ ou ov, hκ _ _ ov ou,
    hκ _ _ ov ov, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have h01 : inner ℝ (partialU c α) (partialV c α) = 0 := horth
  rw [h01, hvu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

/-- **An umbilic from the normal field (for MLS eq. (5.21), p. 245, and Exercise 19, p. 263):** under
the hypotheses of `curvatureTensor_eq_smul_one_of_form`, `α` is an umbilic of `c`: `K₁₂ = 0` and
`K₁₁ = K₂₂`. -/
theorem isUmbilicAt_of_form {G : Vec3 → Vec3} (hc : DifferentiableAt ℝ c α)
    (hG : DifferentiableAt ℝ G (c α)) (h0 : G (c α) ≠ 0)
    (hn : gaussNormal c =ᶠ[𝓝 α] fun β => normalizedField G (c β)) (horth : IsOrthogonalAt c α)
    (hu : partialU c α ≠ 0) (hv : partialV c α ≠ 0) {κ : ℝ}
    (hκ : ∀ w w' : Vec3, inner ℝ w (G (c α)) = 0 → inner ℝ w' (G (c α)) = 0 →
      inner ℝ w (fderiv ℝ G (c α) w') = κ * inner ℝ w w') :
    IsUmbilicAt c α := by
  have hK := curvatureTensor_eq_smul_one_of_form hc hG h0 hn horth hu hv hκ
  refine ⟨?_, ?_⟩ <;> rw [hK] <;> simp

end Surface
end RoboLean
