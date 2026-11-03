import RoboLean.Geometry.RotationSurjectivity

/-!
# Projection maps and the null space of `I - e^{ω̂θ}` (MLS Chapter 2, Exercise 9(a)–(c))

MLS Chapter 2, Exercise 9, printed p. 75, "Projection maps and proof of Proposition 2.9", for a
unit vector `ω` (`‖ω‖ = 1`), `N_ω` the span of `ω` and `N_ω^⊥` its orthogonal complement:

* (a) `image ω̂ = N_ω^⊥` and `kernel ω̂ = N_ω` (with `ω̂ v = ω × v`, eq. (2.4), p. 26);
* (b) a projection map onto a subspace `V` is a linear map onto `V` that fixes `V`; `P_{N_ω} = ωωᵀ`
  and `P_{N_ω^⊥} = I - ωωᵀ` are projection maps (here `ωωᵀ x = (ωᵀx) ω`, `Vec3.outer ω ω`);
* (c) for `θ ∈ (0, 2π)` the null space of `I - e^{ω̂θ}` is `N_ω`, and `I - e^{ω̂θ}` maps `N_ω^⊥`
  bijectively onto `N_ω^⊥`.

Part (d) is the invertibility of `A = (I - e^{ω̂θ}) ω̂ + ωωᵀθ`, already in the library
(`translationJacobian`). Vectors are the library's `Vec3` (Euclidean three-space) with its inner
product; spans are written with scalar multiples (`v = c • ω`) and orthogonal complements with
`inner ℝ ω u = 0`. The inverse on `N_ω^⊥` is explicit:
`u ↦ u/2 + (sin θ / (2 (1 - cos θ))) ω × u`.
-/

noncomputable section

open Matrix Real

namespace RoboLean.Rotation

/-- The inner product of Euclidean three-space in coordinates (MLS p. 23). -/
private theorem inner_eq_dot (x y : Vec3) :
    inner ℝ x y = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/-- A unit vector has `ωᵀω = 1` (MLS p. 26). -/
private theorem inner_self_of_norm {ω : Vec3} (hω : ‖ω‖ = 1) : inner ℝ ω ω = 1 := by
  rw [real_inner_self_eq_norm_sq, hω, one_pow]

/-- `ω · (ω × u) = 0` (MLS p. 26). -/
private theorem inner_cross_self (ω u : Vec3) : inner ℝ ω (Vec3.cross ω u) = 0 := by
  rw [inner_eq_dot, Vec3.cross_coordinates, dot_self_cross]

/-- `u · (ω × u) = 0` (MLS p. 26). -/
private theorem inner_cross_self' (ω u : Vec3) : inner ℝ u (Vec3.cross ω u) = 0 := by
  rw [inner_eq_dot, Vec3.cross_coordinates, dot_cross_self]

/-- `ω × (ω × u) = (ω · u) ω - u` for a unit vector `ω` (MLS p. 26, eq. (2.4) twice). -/
private theorem cross_cross_self {ω : Vec3} (hω : ‖ω‖ = 1) (u : Vec3) :
    Vec3.cross ω (Vec3.cross ω u) = inner ℝ ω u • ω - u := by
  have h1 := inner_self_of_norm hω
  rw [inner_eq_dot] at h1
  apply WithLp.ofLp_injective
  rw [Vec3.cross_coordinates, Vec3.cross_coordinates, cross_cross_eq_smul_sub_smul', h1, one_smul,
    WithLp.ofLp_sub, WithLp.ofLp_smul, inner_eq_dot]

/-- **MLS Exercise 9(a)**, printed p. 75: `kernel ω̂ = N_ω` for a unit vector `ω`: `ω × v = 0`
exactly when `v` is a multiple of `ω` (`ω̂ v = ω × v`, eq. (2.4), p. 26). -/
theorem cross_eq_zero_iff_of_norm_eq_one {ω : Vec3} (hω : ‖ω‖ = 1) (v : Vec3) :
    Vec3.cross ω v = 0 ↔ ∃ c : ℝ, v = c • ω := by
  constructor
  · intro h
    refine ⟨inner ℝ ω v, ?_⟩
    have := cross_cross_self hω v
    rw [h] at this
    have h0 : Vec3.cross ω 0 = 0 := by
      apply WithLp.ofLp_injective
      simp [Vec3.cross_coordinates]
    rw [h0] at this
    exact (sub_eq_zero.1 this.symm).symm
  · rintro ⟨c, rfl⟩
    apply WithLp.ofLp_injective
    simp [Vec3.cross_coordinates, cross_self]

/-- **MLS Exercise 9(a)**, printed p. 75: `image ω̂ = N_ω^⊥` for a unit vector `ω`: `u = ω × v` for
some `v` exactly when `u` is orthogonal to `ω` (`ω̂ v = ω × v`, eq. (2.4), p. 26). -/
theorem exists_cross_eq_iff_of_norm_eq_one {ω : Vec3} (hω : ‖ω‖ = 1) (u : Vec3) :
    (∃ v, Vec3.cross ω v = u) ↔ inner ℝ ω u = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact inner_cross_self ω v
  · intro hu
    refine ⟨Vec3.cross u ω, ?_⟩
    have h1 := inner_self_of_norm hω
    rw [inner_eq_dot] at h1 hu
    apply WithLp.ofLp_injective
    rw [Vec3.cross_coordinates, Vec3.cross_coordinates, cross_cross_eq_smul_sub_smul', h1,
      dotProduct_comm, hu, one_smul, zero_smul, sub_zero]

/-- MLS Exercise 9(b), printed p. 75: the matrix `ωωᵀ` acts by `x ↦ (ωᵀx) ω`. -/
theorem outer_self_mulVec (ω x : Vec3) :
    Vec3.outer ω ω *ᵥ WithLp.ofLp x = WithLp.ofLp (inner ℝ ω x • ω) := by
  ext i
  simp [Vec3.outer, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, inner_eq_dot,
    Fin.sum_univ_three]
  ring

/-- **MLS Exercise 9(b)**, printed p. 75: `P_{N_ω} = ωωᵀ` is a projection map onto `N_ω` for a
unit vector `ω`: its image is `N_ω` and it fixes every vector of `N_ω`. -/
theorem axisProjection_isProjection {ω : Vec3} (hω : ‖ω‖ = 1) :
    (∀ y : Vec3, (∃ x : Vec3, inner ℝ ω x • ω = y) ↔ ∃ c : ℝ, y = c • ω) ∧
      ∀ c : ℝ, inner ℝ ω (c • ω) • ω = c • ω := by
  refine ⟨fun y => ⟨?_, ?_⟩, fun c => ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c • ω, by rw [inner_smul_right, inner_self_of_norm hω, mul_one]⟩
  · rw [inner_smul_right, inner_self_of_norm hω, mul_one]

/-- **MLS Exercise 9(b)**, printed p. 75: `P_{N_ω^⊥} = I - ωωᵀ` is a projection map onto `N_ω^⊥`
for a unit vector `ω`: its image is `N_ω^⊥` and it fixes every vector orthogonal to `ω`. -/
theorem perpProjection_isProjection {ω : Vec3} (hω : ‖ω‖ = 1) :
    (∀ y : Vec3, (∃ x : Vec3, x - inner ℝ ω x • ω = y) ↔ inner ℝ ω y = 0) ∧
      ∀ x : Vec3, inner ℝ ω x = 0 → x - inner ℝ ω x • ω = x := by
  refine ⟨fun y => ⟨?_, ?_⟩, fun x hx => ?_⟩
  · rintro ⟨x, rfl⟩
    rw [inner_sub_right, inner_smul_right, inner_self_of_norm hω, mul_one, sub_self]
  · intro hy
    exact ⟨y, by rw [hy, zero_smul, sub_zero]⟩
  · rw [hx, zero_smul, sub_zero]

/-- **MLS Exercise 9(c)**, printed p. 75: for a unit vector `ω` and `θ ∈ (0, 2π)` the null space
of `I - e^{ω̂θ}` is `N_ω`: `e^{ω̂θ} x = x` exactly when `x` is a multiple of `ω`. -/
theorem exp_act_eq_self_iff {ω : Vec3} (hω : ‖ω‖ = 1) {θ : ℝ} (h0 : 0 < θ) (h2 : θ < 2 * π)
    (x : Vec3) :
    (exp ω θ).act x = x ↔ ∃ c : ℝ, x = c • ω := by
  constructor
  · intro hx
    refine ⟨inner ℝ ω x, ?_⟩
    set p := Vec3.perp ω x with hp
    have hxp : x = inner ℝ ω x • ω + p := by simp [hp, Vec3.perp]
    have hpω : inner ℝ ω p = 0 := Vec3.inner_perp hω x
    rw [exp_act_eq hω θ x, ← hp] at hx
    have key : (cos θ - 1) • p + sin θ • Vec3.cross ω p = 0 := by
      linear_combination (norm := module) hx + hxp
    have hin := congrArg (fun z => inner ℝ p z) key
    simp only [inner_add_right, inner_smul_right, inner_cross_self', inner_zero_right,
      mul_zero, add_zero] at hin
    have hc : cos θ ≠ 1 := by
      intro hc
      have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) h2).1 hc
      linarith
    have hpp : inner ℝ p p = 0 := by
      rcases mul_eq_zero.1 hin with h | h
      · exact absurd (sub_eq_zero.1 h) hc
      · exact h
    have hp0 : p = 0 := inner_self_eq_zero.1 hpp
    rw [hp0, add_zero] at hxp
    exact hxp
  · rintro ⟨c, rfl⟩
    rw [map_smul, exp_act_unit_axis ω hω]

/-- MLS Exercise 9(c), printed p. 75: `I - e^{ω̂θ}` maps every vector into `N_ω^⊥`, in particular
`N_ω^⊥` into itself (unit `ω`, any `θ`). -/
theorem inner_sub_exp_act {ω : Vec3} (hω : ‖ω‖ = 1) (θ : ℝ) (y : Vec3) :
    inner ℝ ω (y - (exp ω θ).act y) = 0 := by
  rw [inner_sub_right, inner_exp_act_axis hω, sub_self]

/-- **MLS Exercise 9(c)**, printed p. 75: for a unit vector `ω` and `θ ∈ (0, 2π)`,
`I - e^{ω̂θ} : N_ω^⊥ → N_ω^⊥` is bijective: every `u ⊥ ω` is `y - e^{ω̂θ} y` for exactly one
`y ⊥ ω`. -/
theorem existsUnique_sub_exp_act {ω : Vec3} (hω : ‖ω‖ = 1) {θ : ℝ} (h0 : 0 < θ)
    (h2 : θ < 2 * π) {u : Vec3} (hu : inner ℝ ω u = 0) :
    ∃! y : Vec3, inner ℝ ω y = 0 ∧ y - (exp ω θ).act y = u := by
  have hc : cos θ ≠ 1 := by
    intro hc
    have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) h2).1 hc
    linarith
  have hc1 : 1 - cos θ ≠ 0 := sub_ne_zero.2 (Ne.symm hc)
  have hR : ∀ y : Vec3, inner ℝ ω y = 0 →
      y - (exp ω θ).act y = (1 - cos θ) • y - sin θ • Vec3.cross ω y := by
    intro y hy
    rw [exp_act_of_inner_eq_zero ω y hω hy]
    module
  have inj : ∀ y z : Vec3, inner ℝ ω y = 0 → inner ℝ ω z = 0 →
      y - (exp ω θ).act y = z - (exp ω θ).act z → y = z := by
    intro y z hy hz hyz
    have hd : (exp ω θ).act (y - z) = y - z := by
      rw [map_sub]
      linear_combination (norm := module) -hyz
    obtain ⟨c, hc⟩ := (exp_act_eq_self_iff hω h0 h2 _).1 hd
    have hi : inner ℝ ω (y - z) = 0 := by rw [inner_sub_right, hy, hz, sub_self]
    rw [hc, inner_smul_right, inner_self_of_norm hω, mul_one] at hi
    rw [hi, zero_smul] at hc
    exact sub_eq_zero.1 hc
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Vec3,
      y₀ = (1 / 2 : ℝ) • u + (sin θ / (2 * (1 - cos θ))) • Vec3.cross ω u := ⟨_, rfl⟩
  have hy₀ω : inner ℝ ω y₀ = 0 := by
    rw [hy₀, inner_add_right, inner_smul_right, inner_smul_right, hu, inner_cross_self]
    ring
  have hy₀u : y₀ - (exp ω θ).act y₀ = u := by
    rw [hR _ hy₀ω, hy₀]
    have hcr : Vec3.cross ω ((1 / 2 : ℝ) • u + (sin θ / (2 * (1 - cos θ))) • Vec3.cross ω u) =
        (1 / 2 : ℝ) • Vec3.cross ω u - (sin θ / (2 * (1 - cos θ))) • u := by
      have hl : ∀ (a b : ℝ) (x z : Vec3), Vec3.cross ω (a • x + b • z) =
          a • Vec3.cross ω x + b • Vec3.cross ω z := by
        intro a b x z
        apply WithLp.ofLp_injective
        simp [Vec3.cross_coordinates]
      rw [hl, cross_cross_self hω, hu, zero_smul, zero_sub, smul_neg]
      abel
    rw [hcr]
    have e1 : (1 - cos θ) * (1 / 2) + sin θ * (sin θ / (2 * (1 - cos θ))) = 1 := by
      field_simp
      nlinarith [sin_sq_add_cos_sq θ]
    have e2 : (1 - cos θ) * (sin θ / (2 * (1 - cos θ))) - sin θ * (1 / 2) = 0 := by
      field_simp
      ring
    calc (1 - cos θ) • ((1 / 2 : ℝ) • u + (sin θ / (2 * (1 - cos θ))) • Vec3.cross ω u) -
          sin θ • ((1 / 2 : ℝ) • Vec3.cross ω u - (sin θ / (2 * (1 - cos θ))) • u)
        = ((1 - cos θ) * (1 / 2) + sin θ * (sin θ / (2 * (1 - cos θ)))) • u +
          ((1 - cos θ) * (sin θ / (2 * (1 - cos θ))) - sin θ * (1 / 2)) • Vec3.cross ω u := by
          module
      _ = u := by rw [e1, e2, one_smul, zero_smul, add_zero]
  exact ⟨y₀, ⟨hy₀ω, hy₀u⟩, fun y hy => inj y y₀ hy.1 hy₀ω (hy.2.trans hy₀u.symm)⟩

end RoboLean.Rotation
