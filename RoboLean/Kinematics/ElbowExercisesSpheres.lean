import RoboLean.Kinematics.PadenKahanVariants

/-!
# Subproblem 4: the three spheres of the hint meet in at most two points

MLS Chapter 3, Exercise 6, printed pp. 147–148, Figure 3.25. Subproblem 4 asks for `θ₁, θ₂` with
`‖e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} p − q₁‖ = δ₁` and `‖e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} p − q₂‖ = δ₂` for zero-pitch unit twists
whose axes meet at `r`; the hint is to find the image point `q` on "the intersection of the three
spheres centered at, respectively, `q₁`, `q₂`, and `r`, of radii `δ₁`, `δ₂`, and `‖p − r‖`". The
library states the hint as an equivalence (`PadenKahan.subproblemFour_iff`). This file proves the
count: when the three centres are not collinear (`(q₂ − q₁) × (r − q₁) ≠ 0`), three spheres share at
most two points, so the solutions of Subproblem 4 have at most two image points.

"At most two points" is stated in the pigeonhole form: among any three common points two are
equal. The radii are arbitrary reals (a negative radius gives an empty sphere).
-/

noncomputable section

open Matrix

namespace RoboLean
namespace PadenKahan

private theorem inner_sub_eq_zero_of_two_spheres {x y q₁ q₂ : Vec3}
    (h₁ : ‖x - q₁‖ = ‖y - q₁‖) (h₂ : ‖x - q₂‖ = ‖y - q₂‖) :
    inner ℝ (y - x) (q₂ - q₁) = 0 := by
  have e₁ := congrArg (· ^ 2) h₁
  have e₂ := congrArg (· ^ 2) h₂
  simp only [norm_sub_sq_real] at e₁ e₂
  simp only [inner_sub_left, inner_sub_right] at e₁ e₂ ⊢
  linarith

private theorem smul_eq_of_inner_eq_zero {a u v : Vec3} (hu : inner ℝ a u = 0)
    (hv : inner ℝ a v = 0) :
    inner ℝ (Vec3.cross u v) (Vec3.cross u v) • a =
      inner ℝ a (Vec3.cross u v) • Vec3.cross u v := by
  have hzero : crossProduct (WithLp.ofLp a) (crossProduct (WithLp.ofLp u) (WithLp.ofLp v)) = 0 := by
    rw [cross_cross_eq_smul_sub_smul']
    have hu' : WithLp.ofLp a ⬝ᵥ WithLp.ofLp u = 0 := by
      simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hu
    have hv' : WithLp.ofLp a ⬝ᵥ WithLp.ofLp v = 0 := by
      simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hv
    rw [hv', dotProduct_comm, hu', zero_smul, zero_smul, sub_zero]
  have key := cross_cross_eq_smul_sub_smul' (crossProduct (WithLp.ofLp u) (WithLp.ofLp v))
    (WithLp.ofLp a) (crossProduct (WithLp.ofLp u) (WithLp.ofLp v))
  rw [hzero, map_zero] at key
  apply WithLp.ofLp_injective
  simp only [WithLp.ofLp_smul, Vec3.cross_coordinates, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial]
  rw [dotProduct_comm _ (WithLp.ofLp a)]
  exact sub_eq_zero.mp key.symm

/-- **MLS Exercise 6, pp. 147–148 (Subproblem 4, the hint): three spheres with non-collinear centres
meet in at most two points.** If `(q₂ − q₁) × (r − q₁) ≠ 0` and `x`, `y`, `z` each lie on the spheres
of radii `δ₁`, `δ₂`, `δ₃` about `q₁`, `q₂`, `r`, then two of `x`, `y`, `z` are equal. -/
theorem eq_or_eq_of_mem_three_spheres {q₁ q₂ r : Vec3}
    (hn : Vec3.cross (q₂ - q₁) (r - q₁) ≠ 0) {δ₁ δ₂ δ₃ : ℝ} {x y z : Vec3}
    (hx : ‖x - q₁‖ = δ₁ ∧ ‖x - q₂‖ = δ₂ ∧ ‖x - r‖ = δ₃)
    (hy : ‖y - q₁‖ = δ₁ ∧ ‖y - q₂‖ = δ₂ ∧ ‖y - r‖ = δ₃)
    (hz : ‖z - q₁‖ = δ₁ ∧ ‖z - q₂‖ = δ₂ ∧ ‖z - r‖ = δ₃) :
    x = y ∨ x = z ∨ y = z := by
  obtain ⟨hx₁, hx₂, hx₃⟩ := hx
  obtain ⟨hy₁, hy₂, hy₃⟩ := hy
  obtain ⟨hz₁, hz₂, hz₃⟩ := hz
  set n := Vec3.cross (q₂ - q₁) (r - q₁) with hn_def
  have hN : inner ℝ n n ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)
  -- the difference of two common points is a multiple of `n`, with a quadratic condition on the factor
  have step : ∀ a : Vec3, ‖a - q₁‖ = δ₁ → ‖a - q₂‖ = δ₂ → ‖a - r‖ = δ₃ →
      inner ℝ n n • (a - x) = inner ℝ (a - x) n • n ∧
        inner ℝ (a - x) n * (2 * inner ℝ (x - r) n + inner ℝ (a - x) n) = 0 := by
    intro a ha₁ ha₂ ha₃
    have hu := inner_sub_eq_zero_of_two_spheres (x := x) (y := a) (q₁ := q₁) (q₂ := q₂)
      (by rw [hx₁, ha₁]) (by rw [hx₂, ha₂])
    have hv := inner_sub_eq_zero_of_two_spheres (x := x) (y := a) (q₁ := q₁) (q₂ := r)
      (by rw [hx₁, ha₁]) (by rw [hx₃, ha₃])
    have e := smul_eq_of_inner_eq_zero hu hv
    refine ⟨e, ?_⟩
    have hE : 2 * inner ℝ (x - r) (a - x) + inner ℝ (a - x) (a - x) = 0 := by
      have h := congrArg (· ^ 2) (ha₃.trans hx₃.symm)
      rw [show a - r = (x - r) + (a - x) by abel, norm_add_sq_real,
        ← real_inner_self_eq_norm_sq (a - x)] at h
      linarith
    have h1 : inner ℝ n n * inner ℝ (x - r) (a - x) = inner ℝ (a - x) n * inner ℝ (x - r) n := by
      have := congrArg (inner ℝ (x - r)) e
      simpa only [inner_smul_right] using this
    have h2 : inner ℝ n n ^ 2 * inner ℝ (a - x) (a - x) = inner ℝ (a - x) n ^ 2 * inner ℝ n n := by
      have := congrArg (fun w => inner ℝ w w) e
      simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real] at this
      linear_combination this
    have h3 : inner ℝ n n * (inner ℝ (a - x) n * (2 * inner ℝ (x - r) n + inner ℝ (a - x) n)) = 0 := by
      linear_combination inner ℝ n n ^ 2 * hE - 2 * inner ℝ n n * h1 - h2
    exact (mul_eq_zero.mp h3).resolve_left hN
  obtain ⟨ey, ry⟩ := step y hy₁ hy₂ hy₃
  obtain ⟨ez, rz⟩ := step z hz₁ hz₂ hz₃
  have eq_of : ∀ a : Vec3, inner ℝ n n • (a - x) = inner ℝ (a - x) n • n →
      inner ℝ (a - x) n = 0 → x = a := by
    intro a ea h0
    rw [h0, zero_smul] at ea
    exact (sub_eq_zero.mp ((smul_eq_zero.mp ea).resolve_left hN)).symm
  rcases mul_eq_zero.mp ry with hs | hs
  · exact Or.inl (eq_of y ey hs)
  rcases mul_eq_zero.mp rz with ht | ht
  · exact Or.inr (Or.inl (eq_of z ez ht))
  right; right
  have hst : inner ℝ (y - x) n = inner ℝ (z - x) n := by linarith
  have : inner ℝ n n • (y - x) = inner ℝ n n • (z - x) := by rw [ey, ez, hst]
  have := smul_right_injective Vec3 hN this
  simpa using this

/-- **MLS Exercise 6, pp. 147–148: Subproblem 4 has at most two image points.** For zero-pitch unit
twists with axes through `r`, and `q₁`, `q₂`, `r` not collinear, among any three solutions
`(θ₁, θ₂)`, `(θ₁′, θ₂′)`, `(θ₁″, θ₂″)` of the two distance equations, two have the same image point
`e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} p`. -/
theorem subproblemFour_image_eq_or_eq {ω₁ ω₂ : Vec3} (hω₁ : ‖ω₁‖ = 1) (hω₂ : ‖ω₂‖ = 1)
    {r p q₁ q₂ : Vec3} (hn : Vec3.cross (q₂ - q₁) (r - q₁) ≠ 0) {δ₁ δ₂ : ℝ}
    (θ θ' θ'' : ℝ × ℝ)
    (h : ∀ t ∈ ({θ, θ', θ''} : Set (ℝ × ℝ)),
      ‖(Twist.exp (Twist.revolute ω₁ r) t.1 * Twist.exp (Twist.revolute ω₂ r) t.2).applyPoint p -
          q₁‖ = δ₁ ∧
        ‖(Twist.exp (Twist.revolute ω₁ r) t.1 * Twist.exp (Twist.revolute ω₂ r) t.2).applyPoint p -
          q₂‖ = δ₂) :
    let c := fun t : ℝ × ℝ =>
      (Twist.exp (Twist.revolute ω₁ r) t.1 * Twist.exp (Twist.revolute ω₂ r) t.2).applyPoint p
    c θ = c θ' ∨ c θ = c θ'' ∨ c θ' = c θ'' := by
  intro c
  have hr : ∀ t : ℝ × ℝ, ‖c t - r‖ = ‖p - r‖ := by
    intro t
    obtain ⟨c', -, -, hc', hc⟩ :=
      (subproblemFour_iff hω₁ hω₂ r p q₁ q₂ _ _ t.1 t.2).mp ⟨rfl, rfl⟩
    rw [← hc] at hc'
    exact hc'
  have mem : ∀ t ∈ ({θ, θ', θ''} : Set (ℝ × ℝ)),
      ‖c t - q₁‖ = δ₁ ∧ ‖c t - q₂‖ = δ₂ ∧ ‖c t - r‖ = ‖p - r‖ := fun t ht =>
    ⟨(h t ht).1, (h t ht).2, hr t⟩
  exact eq_or_eq_of_mem_three_spheres hn (mem θ (by simp)) (mem θ' (by simp)) (mem θ'' (by simp))

end PadenKahan
end RoboLean
