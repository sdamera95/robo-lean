import RoboLean.Kinematics.Singularity
import RoboLean.Kinematics.ForcePullback

/-!
# Balanced wrenches and further singular configurations (MLS Exercises 15–17 and 19)

MLS §3.8, printed pp. 150–151.

* Exercise 19: at a singular configuration some nonzero end-effector wrench is balanced
  without joint torques, `τ = (Jˢ)ᵀ F = 0` (MLS eq. (3.60), p. 121), and the wrench is
  reciprocal to every column of the Jacobian, `F · ξᵢ' = 0` (the pairing of MLS p. 61). For a
  chain with at least six joints the existence of such a wrench characterizes the singular
  configurations. The body form follows by the wrench transformation (MLS eq. (2.67), p. 63).
* Exercise 16: six revolute joint axes that all meet one line give a singular configuration;
  the zero-pitch wrench along the line, `F = (ν, p × ν)`, is balanced.
* Exercise 17: a prismatic joint normal to the plane of two parallel revolute axes gives a
  singular configuration; the difference of the two revolute twists is a multiple of the
  prismatic twist.
* Exercise 15: four coplanar revolute joint axes give a singular configuration; the four
  columns lie in a three-dimensional space of twists.

The columns of the spatial Jacobian are the joint twists in the current configuration
(MLS p. 116); the book writes a revolute twist as `(q × ω, ω)`, which is
`Twist.revolute ω q = (-ω × q, ω)`. Conventions: twists `(v, ω)`, wrenches `(f, τ)` with the
moment about the base origin, Lean column `i` is the book's column `i + 1`, real joint lift.
-/

noncomputable section

open Module
open scoped Matrix

namespace RoboLean

namespace SerialChain

variable {n : ℕ}

/-- A real matrix with six columns has rank less than six exactly when it annihilates a nonzero
vector. -/
private theorem rank_lt_six_iff {m : Type*} [Fintype m] (A : Matrix m (Fin 3 ⊕ Fin 3) ℝ) :
    A.rank < 6 ↔ ∃ x : Fin 3 ⊕ Fin 3 → ℝ, x ≠ 0 ∧ A *ᵥ x = 0 := by
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h6 : finrank ℝ (Fin 3 ⊕ Fin 3 → ℝ) = 6 := by simp
  rw [h6] at h
  rw [Matrix.rank]
  constructor
  · intro hr
    have hk : LinearMap.ker A.mulVecLin ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at h
      omega
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
    exact ⟨x, hx0, by simpa using hx⟩
  · rintro ⟨x, hx0, hx⟩
    have hk : LinearMap.ker A.mulVecLin ≠ ⊥ := by
      intro hb
      have : x ∈ LinearMap.ker A.mulVecLin := by simpa using hx
      rw [hb, Submodule.mem_bot] at this
      exact hx0 this
    have : finrank ℝ (LinearMap.ker A.mulVecLin) ≠ 0 := by
      rwa [Ne, Submodule.finrank_eq_zero]
    omega

/-- **MLS Exercise 19, p. 151, rank form.** If the spatial Jacobian has rank less than six, some
nonzero spatial wrench `F` is balanced with zero joint torques, `(Jˢ)ᵀ F = 0` (MLS eq. (3.60),
p. 121), i.e. `F` is reciprocal to every column `ξᵢ'` of the Jacobian (`F · ξᵢ' = 0`, the pairing
of MLS p. 61). -/
theorem exists_balanced_wrench_of_rank_lt (c : SerialChain n) (θ : Fin n → ℝ)
    (h : (c.spatialJacobianMatrix θ).rank < 6) :
    ∃ F : Wrench, F ≠ 0 ∧ c.spatialWrenchTorques θ F = 0 ∧
      ∀ i, Wrench.pair F (c.spatialJacobian θ i) = 0 := by
  rw [← Matrix.rank_transpose, rank_lt_six_iff] at h
  obtain ⟨x, hx0, hx⟩ := h
  refine ⟨Wrench.coordinatesEquiv.symm x, ?_, ?_, ?_⟩
  · intro hF
    apply hx0
    rw [← Wrench.coordinatesEquiv.apply_symm_apply x, hF, map_zero]
  · rw [← spatialJacobianMatrix_transpose_mulVec, ← Wrench.coordinatesEquiv_apply,
      LinearEquiv.apply_symm_apply, hx]
  · intro i
    have := congrFun (show c.spatialWrenchTorques θ (Wrench.coordinatesEquiv.symm x) = 0 by
      rw [← spatialJacobianMatrix_transpose_mulVec, ← Wrench.coordinatesEquiv_apply,
        LinearEquiv.apply_symm_apply, hx]) i
    exact this

/-- **MLS Exercise 19, p. 151.** At a singular configuration (MLS p. 123) some nonzero spatial
wrench is balanced without applying any joint torques, `(Jˢ)ᵀ F = 0`, and it is reciprocal to
every twist `ξᵢ'` forming a column of the Jacobian. -/
theorem exists_balanced_wrench_of_isSingular (c : SerialChain n) (θ : Fin n → ℝ)
    (h : c.IsSingular θ) :
    ∃ F : Wrench, F ≠ 0 ∧ c.spatialWrenchTorques θ F = 0 ∧
      ∀ i, Wrench.pair F (c.spatialJacobian θ i) = 0 :=
  c.exists_balanced_wrench_of_rank_lt θ (lt_of_lt_of_le h (min_le_left 6 n))

/-- **MLS Exercise 19, p. 151, body form.** At a singular configuration some nonzero body
wrench (at the tool origin, in tool coordinates) is balanced without joint torques,
`(Jᵇ)ᵀ F_t = 0` (MLS eq. (3.59), p. 121); it is reciprocal to every body Jacobian column. -/
theorem exists_balanced_bodyWrench_of_isSingular (c : SerialChain n) (θ : Fin n → ℝ)
    (h : c.IsSingular θ) :
    ∃ F : Wrench, F ≠ 0 ∧ c.bodyWrenchTorques θ F = 0 ∧
      ∀ i, Wrench.pair F (c.bodyJacobian θ i) = 0 := by
  obtain ⟨F, hF, hτ, -⟩ := c.exists_balanced_wrench_of_isSingular θ h
  have hb : c.bodyWrenchTorques θ (Wrench.transform (c.fk θ)⁻¹ F) = 0 := by
    rw [bodyWrenchTorques_transform_inv, hτ]
  refine ⟨Wrench.transform (c.fk θ)⁻¹ F, ?_, hb, fun i => congrFun hb i⟩
  intro h0
  apply hF
  have := congrArg (Wrench.transform (c.fk θ)) h0
  simpa using this

/-- **MLS Exercise 19, p. 151, converse for at least six joints.** For a chain with `n ≥ 6`
joints, a nonzero spatial wrench balanced with zero joint torques forces a singular
configuration (MLS p. 123). -/
theorem isSingular_of_balanced_wrench (c : SerialChain n) (θ : Fin n → ℝ) (hn : 6 ≤ n)
    (F : Wrench) (hF : F ≠ 0) (hτ : c.spatialWrenchTorques θ F = 0) : c.IsSingular θ := by
  rw [IsSingular, min_eq_left hn, ← Matrix.rank_transpose, rank_lt_six_iff]
  refine ⟨F.coordinates, ?_, by rw [spatialJacobianMatrix_transpose_mulVec, hτ]⟩
  intro h0
  apply hF
  apply Wrench.coordinatesEquiv.injective
  rw [map_zero, Wrench.coordinatesEquiv_apply]
  exact h0

/-- **MLS Exercise 19, p. 151, and p. 123.** For a chain with at least six joints, a
configuration is singular exactly when some nonzero spatial wrench is balanced without joint
torques. -/
theorem isSingular_iff_exists_balanced_wrench (c : SerialChain n) (θ : Fin n → ℝ)
    (hn : 6 ≤ n) :
    c.IsSingular θ ↔ ∃ F : Wrench, F ≠ 0 ∧ c.spatialWrenchTorques θ F = 0 := by
  constructor
  · intro h
    obtain ⟨F, hF, hτ, -⟩ := c.exists_balanced_wrench_of_isSingular θ h
    exact ⟨F, hF, hτ⟩
  · rintro ⟨F, hF, hτ⟩
    exact c.isSingular_of_balanced_wrench θ hn F hF hτ

/-- The zero-pitch wrench along the line through `p` with direction `ν` is reciprocal to every
revolute twist whose axis meets the line. -/
private theorem pair_line_revolute (p ν ω q : Vec3) (γ β : ℝ) (h : q + γ • ω = p + β • ν) :
    Wrench.pair ⟨ν, Vec3.cross p ν⟩ (Twist.revolute ω q) = 0 := by
  have hq : q = p + β • ν - γ • ω := eq_sub_of_add_eq h
  subst hq
  simp only [Wrench.pair, Twist.revolute, EuclideanSpace.inner_eq_star_dotProduct]
  simp [Vec3.cross_coordinates, cross_apply, dotProduct, Fin.sum_univ_succ]
  ring

private theorem inner_eq_dot' (x y : Vec3) :
    inner ℝ x y = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

private theorem cross_cross_right' (a b c : Vec3) :
    Vec3.cross a (Vec3.cross b c) = inner ℝ a c • b - inner ℝ a b • c := by
  apply WithLp.ofLp_injective
  simp only [Vec3.cross_coordinates, WithLp.ofLp_sub, WithLp.ofLp_smul, inner_eq_dot']
  rw [cross_cross_eq_smul_sub_smul', dotProduct_comm (WithLp.ofLp b)]

/-- A vector `w` whose cross product with a nonzero `v` vanishes is a multiple of `v`. -/
private theorem eq_smul_of_cross_eq_zero {v w : Vec3} (hv : v ≠ 0) (h : Vec3.cross v w = 0) :
    w = (inner ℝ v w / ‖v‖ ^ 2) • v := by
  have h2 := cross_cross_right' v v w
  rw [h, Vec3.cross_zero, real_inner_self_eq_norm_sq] at h2
  have hn : ‖v‖ ^ 2 ≠ 0 := by positivity
  have h3 : ‖v‖ ^ 2 • w = inner ℝ v w • v := (sub_eq_zero.mp h2.symm).symm
  rw [div_eq_inv_mul, mul_smul, ← h3, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- **MLS Exercise 16, p. 151: six revolute joint axes intersecting along a line.** If at the
configuration `θ` every column of the spatial Jacobian is a revolute twist `(-ωᵢ × qᵢ, ωᵢ)`
whose axis meets the line through `p` with direction `ν ≠ 0` (`qᵢ + γᵢ ωᵢ = p + βᵢ ν`, as
printed), the configuration is singular, for every chain with `n ≥ 6` joints (the book's case is
`n = 6`). The zero-pitch wrench along the line, `F = (ν, p × ν)`, is balanced
(Exercise 19). The hypothesis `ν ≠ 0` is the book's "line". -/
theorem isSingular_of_revolute_meet_line (c : SerialChain n) (θ : Fin n → ℝ) (hn : 6 ≤ n)
    (ω qs : Fin n → Vec3) (hcol : ∀ i, c.spatialJacobian θ i = Twist.revolute (ω i) (qs i))
    (p ν : Vec3) (hν : ν ≠ 0) (γ β : Fin n → ℝ)
    (hmeet : ∀ i, qs i + γ i • ω i = p + β i • ν) : c.IsSingular θ := by
  refine c.isSingular_of_balanced_wrench θ hn ⟨ν, Vec3.cross p ν⟩ ?_ ?_
  · intro h
    exact hν (congrArg Wrench.force h)
  · funext i
    change Wrench.pair _ (c.spatialJacobian θ i) = 0
    rw [hcol i]
    exact pair_line_revolute p ν (ω i) (qs i) (γ i) (β i) (hmeet i)

/-- **MLS Exercise 17, p. 151: a prismatic joint perpendicular to two parallel coplanar
revolute joints.** If at the configuration `θ` two distinct columns `i, j` of the spatial
Jacobian are revolute twists `(-ω₁ × q₁, ω₁)`, `(-ω₂ × q₂, ω₂)` and a third column `k` is a
prismatic twist `(v, 0)`, with `vᵀω₁ = 0` (condition (a); its second half `vᵀω₂ = 0` follows
from condition (c)), `vᵀ(q₁ - q₂) = 0` (condition (b)) and `ω₁ = ±ω₂` (condition (c)), the
configuration is singular, for every chain with `n ≤ 6` joints. The three columns are linearly
dependent. -/
theorem isSingular_of_prismatic_normal_parallel_revolute (c : SerialChain n) (θ : Fin n → ℝ)
    (hn : n ≤ 6) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (ω₁ ω₂ q₁ q₂ v : Vec3) (hi : c.spatialJacobian θ i = Twist.revolute ω₁ q₁)
    (hj : c.spatialJacobian θ j = Twist.revolute ω₂ q₂)
    (hk : c.spatialJacobian θ k = Twist.prismatic v)
    (ha₁ : inner ℝ v ω₁ = 0) (hb : inner ℝ v (q₁ - q₂) = 0)
    (hpar : ω₁ = ω₂ ∨ ω₁ = -ω₂) : c.IsSingular θ := by
  rw [c.isSingular_iff_not_linearIndependent θ hn]
  intro hJ
  by_cases hv : v = 0
  · apply hJ.ne_zero k
    rw [hk, hv]
    rfl
  have hvw : Vec3.cross v (Vec3.cross ω₁ (q₁ - q₂)) = 0 := by
    rw [cross_cross_right', hb, ha₁, zero_smul, zero_smul, sub_zero]
  obtain ⟨a, hw⟩ : ∃ a : ℝ, Vec3.cross ω₁ (q₁ - q₂) = a • v :=
    ⟨_, eq_smul_of_cross_eq_zero hv hvw⟩
  have hsub : Vec3.cross ω₁ q₁ - Vec3.cross ω₁ q₂ = a • v := by
    rw [← hw, sub_eq_add_neg, sub_eq_add_neg, ← Vec3.cross_neg, ← Vec3.cross_add]
  have hinj : Function.Injective ![i, j, k] := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [eq_comm]
  have hli := Fintype.linearIndependent_iff.mp (hJ.comp ![i, j, k] hinj)
  have hsum : ∀ g : Fin 3 → ℝ, ∑ x, g x • (c.spatialJacobian θ ∘ ![i, j, k]) x =
      g 0 • Twist.revolute ω₁ q₁ + g 1 • Twist.revolute ω₂ q₂ + g 2 • Twist.prismatic v := by
    intro g
    simp [Fin.sum_univ_succ, hi, hj, hk, add_assoc]
  rcases hpar with h | h
  · have h0 := hli ![1, -1, a] (by
      rw [hsum, ← h]
      apply Twist.ext
      · simp only [Twist.add_linear, Twist.smul_linear, Twist.revolute, Twist.prismatic,
          Twist.zero_linear]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        linear_combination (norm := module) (-1 : ℝ) • hsub
      · simp [Twist.revolute, Twist.prismatic])
    simpa using h0 0
  · have hω : ω₂ = -ω₁ := by rw [h, neg_neg]
    have h0 := hli ![1, 1, a] (by
      rw [hsum, hω]
      apply Twist.ext
      · simp only [Twist.add_linear, Twist.smul_linear, Twist.revolute, Twist.prismatic,
          Twist.zero_linear, Vec3.neg_cross]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        linear_combination (norm := module) (-1 : ℝ) • hsub
      · simp [Twist.revolute, Twist.prismatic])
    simpa using h0 0

/-- Two vectors perpendicular to a unit vector `ν` have their cross product along `ν`. -/
private theorem cross_eq_inner_smul_of_perp' {ν a b : Vec3} (hν : ‖ν‖ = 1)
    (ha : inner ℝ ν a = 0) (hb : inner ℝ ν b = 0) :
    Vec3.cross a b = inner ℝ ν (Vec3.cross a b) • ν := by
  have h0 : Vec3.cross ν (Vec3.cross a b) = 0 := by
    rw [cross_cross_right', ha, hb, zero_smul, zero_smul, sub_zero]
  have h2 := cross_cross_right' ν ν (Vec3.cross a b)
  rw [h0, Vec3.cross_zero, real_inner_self_eq_norm_sq, hν] at h2
  simp only [one_pow, one_smul] at h2
  exact (sub_eq_zero.mp h2.symm).symm

/-- **MLS Exercise 15, pp. 150–151: four coplanar revolute joints.** If at the configuration
`θ` four distinct columns `f 0, …, f 3` of the spatial Jacobian are revolute twists
`(-ωₖ × qₖ, ωₖ)` whose axes lie in a plane with unit normal `ν` (the book's `n`):
`νᵀωₖ = 0` (condition (a)) and `νᵀ(qₖ - qⱼ) = 0` (condition (b)), the configuration is
singular, for every chain with `n ≤ 6` joints. The four columns lie in a three-dimensional
space of twists. -/
theorem isSingular_of_four_coplanar_revolute (c : SerialChain n) (θ : Fin n → ℝ)
    (hn : n ≤ 6) (f : Fin 4 → Fin n) (hf : Function.Injective f) (ω qs : Fin 4 → Vec3)
    (hcol : ∀ k, c.spatialJacobian θ (f k) = Twist.revolute (ω k) (qs k)) (ν : Vec3)
    (hν : ‖ν‖ = 1) (hνω : ∀ k, inner ℝ ν (ω k) = 0)
    (hνq : ∀ k j, inner ℝ ν (qs k - qs j) = 0) : c.IsSingular θ := by
  rw [c.isSingular_iff_not_linearIndependent θ hn]
  intro hJ
  set N : Twist := ⟨ν, 0⟩
  set coef : Fin 4 → ℝ := fun k => inner ℝ ν (Vec3.cross (ω k) (qs k - qs 0))
  have hcross : ∀ k, Vec3.cross (ω k) (qs k - qs 0) = coef k • ν := fun k =>
    cross_eq_inner_smul_of_perp' hν (hνω k) (hνq k 0)
  let P : Vec3 →ₗ[ℝ] Vec3 := LinearMap.id - (innerₛₗ ℝ ν).smulRight ν
  let L : Vec3 →ₗ[ℝ] Twist :=
    Twist.revoluteLinear (qs 0) ∘ₗ P - (innerₛₗ ℝ ν).smulRight N
  have hcomp : c.spatialJacobian θ ∘ f = L ∘ fun k => ω k + coef k • ν := by
    funext k
    have hin : inner ℝ ν (ω k + coef k • ν) = coef k := by
      rw [inner_add_right, hνω k, inner_smul_right, real_inner_self_eq_norm_sq, hν]
      ring
    have hP : P (ω k + coef k • ν) = ω k := by
      simp only [P, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
        innerₛₗ_apply_apply, hin]
      abel
    have hrev : Twist.revolute (ω k) (qs k) = Twist.revolute (ω k) (qs 0) + (-coef k) • N := by
      apply Twist.ext
      · have hq : Vec3.cross (ω k) (qs k) =
            Vec3.cross (ω k) (qs 0) + Vec3.cross (ω k) (qs k - qs 0) := by
          rw [← Vec3.cross_add]
          congr 1
          abel
        simp only [N, Twist.revolute, Twist.add_linear, Twist.smul_linear, hq, hcross k]
        simp only [neg_add, neg_smul]
      · simp [N, Twist.revolute]
    simp only [Function.comp_apply, hcol k, L, LinearMap.sub_apply, LinearMap.comp_apply, hP,
      LinearMap.smulRight_apply, innerₛₗ_apply_apply, hin, Twist.revoluteLinear_apply, hrev]
    rw [neg_smul, sub_eq_add_neg]
  have hg : LinearIndependent ℝ fun k => ω k + coef k • ν :=
    LinearIndependent.of_comp L (hcomp ▸ hJ.comp f hf)
  have hcard := hg.fintype_card_le_finrank
  simp [Vec3] at hcard

end SerialChain

end RoboLean
