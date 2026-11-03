import RoboLean.Kinematics.EulerSingularity
import RoboLean.Geometry.Wrench
import RoboLean.Kinematics.PadenKahan

/-!
# Spherical joints and the Stewart platform (MLS §3.5.4)

MLS printed pp. 138–142 and Exercise 22, p. 153.

* The spherical joint (p. 139): the rigid motion `g(R) = [R, (I - R)q; 0, 1]` about the joint
  centre `q`, a free rotation `R ∈ SO(3)`, and its velocity `Vˢ = (-ω × q, ω)`, written on p. 140
  as `[-e₁ × q, -e₂ × q, -e₃ × q; e₁, e₂, e₃] ω`, a matrix whose "columns are never linearly
  dependent". Three revolute joints with axes through `q` generate motions of this form, but such a
  model has singular configurations (p. 139, "spherical wrists always have singularities when any
  two of the axes become parallel"); for ZYZ axes through the origin `θ = 0` is one
  (`SerialChain.isSingular_eulerChain_zyz`), whereas the spherical joint's three columns are
  independent at every centre.
* One leg of the Stewart platform (eq. (3.72), p. 140): `g_st = g_s(R_s) e^{ξ̂θ} g_t(R_t) g_st(0)`
  with spherical joints at the base pivot `q_s` and at the reference tool pivot
  `p = g_st(0) q_t`, and the prismatic twist `ξ = (u, 0)` along the reference leg direction
  `u = (p - q_s)/L`, `L = ‖p - q_s‖ ≠ 0`. Every solution of the leg's structure equation has leg
  length `‖q_s - g_st q_t‖ = |L + θ|`. The book prints `θᵢ = ‖q_si - g_st q_ti‖` (p. 140), the leg
  length; with `θ = 0` the reference configuration of (3.72), the extension is
  `θ = ‖q_s - g_st q_t‖ - L` (for `L + θ ≥ 0`), which is the printed formula when `θ` is read as
  the leg length `L + θ`.
* The leg Jacobian of (3.73), p. 141: the three columns `(-eₖ × q_s, eₖ)` of the base spherical
  joint, the prismatic column `(w, 0)` along the current leg and the three columns
  `(-eₖ × c, eₖ)` of the tool spherical joint at the current tool pivot `c`. When the current leg
  length is nonzero (`c ≠ q_s`, `w` a nonzero multiple of `c - q_s`) the seven columns span all
  twists: "the Jacobian matrices are never singular as long as `θᵢ` is nonzero" (p. 141, with
  Exercise 22(b), p. 153, "`θᵢ > 0`"), so every tool velocity is produced by every leg.
* The actuator singularity of coplanar legs (p. 141): the actuated prismatic joints transmit pure
  forces along the legs, `(w, c × w)`. If every leg direction is orthogonal to `n ≠ 0`, the force
  `(n, 0)` normal to the plane is not generated; if moreover the tool pivots lie in a plane
  through the base origin with normal `n`, no pure torque about an axis in that plane is
  generated.

Conventions: twists `(v, ω)`, wrenches `(f, τ)` with the moment about the base origin,
`EuclideanSpace.single k 1` the `k`-th unit vector `e_{k+1}`, real joint values.
-/

noncomputable section

open Real

namespace RoboLean

namespace Stewart

private theorem inner_eq_dot_s (x y : Vec3) :
    inner ℝ x y = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

private theorem cross_cross_right_s (a b c : Vec3) :
    Vec3.cross a (Vec3.cross b c) = inner ℝ a c • b - inner ℝ a b • c := by
  apply WithLp.ofLp_injective
  simp only [Vec3.cross_coordinates, WithLp.ofLp_sub, WithLp.ofLp_smul, inner_eq_dot_s]
  rw [cross_cross_eq_smul_sub_smul', dotProduct_comm (WithLp.ofLp b)]

private theorem cross_eq_inner_smul_of_perp_s {ν a b : Vec3} (hν : ‖ν‖ = 1)
    (ha : inner ℝ ν a = 0) (hb : inner ℝ ν b = 0) :
    Vec3.cross a b = inner ℝ ν (Vec3.cross a b) • ν := by
  have h0 : Vec3.cross ν (Vec3.cross a b) = 0 := by
    rw [cross_cross_right_s, ha, hb, zero_smul, zero_smul, sub_zero]
  have h2 := cross_cross_right_s ν ν (Vec3.cross a b)
  rw [h0, Vec3.cross_zero, real_inner_self_eq_norm_sq, hν] at h2
  simp only [one_pow, one_smul] at h2
  exact (sub_eq_zero.mp h2.symm).symm

private theorem decomp_s (d t : Vec3) (hdd : inner ℝ d d ≠ 0) :
    t = (inner ℝ d t / inner ℝ d d) • d + Vec3.cross ((inner ℝ d d)⁻¹ • Vec3.cross d t) d := by
  rw [Vec3.cross_anticomm, Vec3.cross_smul, cross_cross_right_s, smul_sub, smul_smul,
    smul_smul, inv_mul_cancel₀ hdd, one_smul, div_eq_inv_mul]
  abel

private theorem prismatic_add (x y : Vec3) :
    Twist.prismatic (x + y) = Twist.prismatic x + Twist.prismatic y := by
  apply Twist.ext <;> simp [Twist.prismatic]

private theorem prismatic_smul (r : ℝ) (x : Vec3) :
    Twist.prismatic (r • x) = r • Twist.prismatic x := by
  apply Twist.ext <;> simp [Twist.prismatic]

/-- The rigid motion of a spherical joint with centre `q`, MLS p. 139:
`g(R) = [R, (I - R) q; 0, 1]`, `R ∈ SO(3)` free. -/
def sphericalJoint (q : Vec3) (R : Rotation) : RigidTransform :=
  ⟨R, q - R.act q⟩

/-- **MLS p. 139.** A spherical joint fixes its centre: `g(R) q = q`, for every rotation `R`. -/
theorem sphericalJoint_applyPoint_center (q : Vec3) (R : Rotation) :
    (sphericalJoint q R).applyPoint q = q := by
  simp [sphericalJoint, RigidTransform.applyPoint]

/-- **MLS p. 139.** The rigid motions fixing the point `q` are exactly the spherical-joint motions
about `q`: `g q = q` implies `g = g(R)` with `R` the rotation of `g`. -/
theorem eq_sphericalJoint_of_applyPoint_eq {g : RigidTransform} {q : Vec3}
    (h : g.applyPoint q = q) : g = sphericalJoint q g.rotation := by
  apply RigidTransform.ext
  · rfl
  · exact eq_sub_of_add_eq' h

/-- **MLS p. 140: the velocity of a spherical joint in matrix form.** The velocity
`Vˢ = (-ω × q, ω)` (the twist `Twist.revolute ω q`) is `∑ₖ ωₖ (-eₖ × q, eₖ)`, the product of the
matrix `[-e₁ × q, -e₂ × q, -e₃ × q; e₁, e₂, e₃]` with `ω`. -/
theorem revolute_eq_sum_sphericalColumns (ω q : Vec3) :
    Twist.revolute ω q = ∑ k : Fin 3, ω k • Twist.revolute (EuclideanSpace.single k 1) q := by
  have hω : ω = ∑ k : Fin 3, ω k • EuclideanSpace.single k (1 : ℝ) := by
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three]
  conv_lhs => rw [hω]
  rw [← Twist.revoluteLinear_apply, map_sum]
  simp [Twist.revoluteLinear_apply]

/-- **MLS p. 140: "the columns of the matrix which defines `Vˢ` are never linearly dependent".**
The three twists `(-eₖ × q, eₖ)` are linearly independent for every centre `q`. -/
theorem linearIndependent_sphericalColumns (q : Vec3) :
    LinearIndependent ℝ fun k : Fin 3 => Twist.revolute (EuclideanSpace.single k 1) q := by
  let A : Twist →ₗ[ℝ] Vec3 :=
    { toFun := Twist.angular
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply LinearIndependent.of_comp A
  have : A ∘ (fun k : Fin 3 => Twist.revolute (EuclideanSpace.single k 1) q) =
      EuclideanSpace.basisFun (Fin 3) ℝ := by
    funext k
    simp [A, Twist.revolute]
  rw [this]
  exact (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.linearIndependent

/-- **MLS p. 139: three revolute joints whose axes meet at `q` generate spherical-joint motions.**
For unit axes `a, b, c` through `q`, `e^{ξ̂_a α} e^{ξ̂_b β} e^{ξ̂_c γ} = g(e^{âα} e^{b̂β} e^{ĉγ})`, the
spherical joint about `q`. -/
theorem threeRevolute_eq_sphericalJoint {a b c : Vec3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hc : ‖c‖ = 1) (q : Vec3) (α β γ : ℝ) :
    Twist.exp (Twist.revolute a q) α * Twist.exp (Twist.revolute b q) β *
        Twist.exp (Twist.revolute c q) γ =
      sphericalJoint q (Rotation.exp a α * Rotation.exp b β * Rotation.exp c γ) := by
  rw [Twist.exp_revolute a q ha, Twist.exp_revolute b q hb, Twist.exp_revolute c q hc]
  apply RigidTransform.ext
  · simp [sphericalJoint]
  · simp only [sphericalJoint, RigidTransform.mul_translation, RigidTransform.mul_rotation,
      map_sub, Rotation.act_mul]
    abel

/-- **MLS p. 139: the three-revolute model of a spherical joint has singular configurations.**
The ZYZ chain of three revolute joints through the origin is singular at `θ = 0` (two axes
parallel; MLS Exercise 14(a), p. 150), while the spherical joint's three columns are independent
at every centre (`linearIndependent_sphericalColumns`). -/
theorem eulerChain_zyz_isSingular_zero :
    (SerialChain.eulerChain Rotation.zAxis Rotation.yAxis Rotation.zAxis).IsSingular 0 :=
  (SerialChain.isSingular_eulerChain_zyz 0).2.mpr (by simp)

/-- The tool pivot of a Stewart leg in the reference configuration, in base coordinates:
`p = g_st(0) q_t` (MLS p. 140, `q_t` written relative to the tool frame). -/
def refPivot (qt : Vec3) (g₀ : RigidTransform) : Vec3 :=
  g₀.applyPoint qt

/-- The unit direction `u = (p - q_s)/‖p - q_s‖` of a Stewart leg in the reference configuration
(MLS p. 140, the axis of the prismatic twist `ξᵢ`). -/
def legDirection (qs qt : Vec3) (g₀ : RigidTransform) : Vec3 :=
  ‖refPivot qt g₀ - qs‖⁻¹ • (refPivot qt g₀ - qs)

/-- One leg of the structure equation (3.72) of the Stewart platform, MLS p. 140:
`g_s(R_s) e^{ξ̂θ} g_t(R_t) g_st(0)`, with the spherical joint `g_s` about the base pivot `q_s`, the
prismatic joint `ξ = (u, 0)` along the reference leg direction, and the spherical joint `g_t`
about the reference tool pivot `p = g_st(0) q_t`. -/
def legPose (qs qt : Vec3) (g₀ : RigidTransform) (Rs : Rotation) (θ : ℝ) (Rt : Rotation) :
    RigidTransform :=
  sphericalJoint qs Rs * Twist.exp (Twist.prismatic (legDirection qs qt g₀)) θ *
    sphericalJoint (refPivot qt g₀) Rt * g₀

/-- **MLS p. 140: the leg length of a Stewart leg.** For a nondegenerate reference leg
(`p ≠ q_s`, `L = ‖p - q_s‖`), the leg pose maps the tool pivot `q_t` to
`q_s + R_s ((L + θ) u)`, so the distance between the pivots is `‖q_s - g q_t‖ = |L + θ|`, for all
rotations `R_s, R_t` and every real `θ`. -/
theorem norm_sub_legPose_applyPoint (qs qt : Vec3) (g₀ : RigidTransform) (Rs Rt : Rotation)
    (θ : ℝ) (h : refPivot qt g₀ ≠ qs) :
    ‖qs - (legPose qs qt g₀ Rs θ Rt).applyPoint qt‖ = |‖refPivot qt g₀ - qs‖ + θ| := by
  set p := refPivot qt g₀
  set u := legDirection qs qt g₀
  have hL : ‖p - qs‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  have hpu : p - qs = ‖p - qs‖ • u := by
    simp only [u, legDirection, smul_smul, mul_inv_cancel₀ hL, one_smul, p]
  have hu : ‖u‖ = 1 := by
    simp only [u, legDirection, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hL, p]
  have happ : (legPose qs qt g₀ Rs θ Rt).applyPoint qt = Rs.act (p - qs + θ • u) + qs := by
    simp only [legPose, RigidTransform.mul_applyPoint]
    rw [show g₀.applyPoint qt = p from rfl, sphericalJoint_applyPoint_center, Twist.exp_prismatic]
    simp [sphericalJoint, RigidTransform.applyPoint, map_sub, map_add]
    abel
  rw [happ, sub_add_cancel_right, norm_neg, Rotation.norm_act]
  conv_lhs => rw [hpu]
  rw [← add_smul, norm_smul, hu, mul_one, Real.norm_eq_abs]

/-- **MLS p. 140: inverse kinematics of the Stewart platform, corrected printing.** If the tool
pose `g_st` satisfies the structure equation (3.72) of a leg with extension `θ` and nonnegative
leg length `L + θ ≥ 0`, then `θ = ‖q_s - g_st q_t‖ - L`, i.e. the leg length `L + θ` is the
printed `‖q_si - g_st q_ti‖`. -/
theorem legExtension_eq (qs qt : Vec3) (g₀ g : RigidTransform) (Rs Rt : Rotation) (θ : ℝ)
    (h : refPivot qt g₀ ≠ qs) (hθ : 0 ≤ ‖refPivot qt g₀ - qs‖ + θ)
    (hg : legPose qs qt g₀ Rs θ Rt = g) :
    θ = ‖qs - g.applyPoint qt‖ - ‖refPivot qt g₀ - qs‖ := by
  rw [← hg, norm_sub_legPose_applyPoint qs qt g₀ Rs Rt θ h, abs_of_nonneg hθ]
  ring

/-- Every unit vector is carried to every other unit vector by some rotation (the axis orthogonal
to both, MLS p. 100, Subproblem 1). -/
private theorem exists_rotation_act_eq {u w : Vec3} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    ∃ R : Rotation, R.act u = w := by
  set K : Submodule ℝ Vec3 := Submodule.span ℝ (Set.range ![u, w])
  have hK : Module.finrank ℝ K ≤ 2 := by
    have : Module.finrank ℝ K ≤ Fintype.card (Fin 2) := finrank_range_le_card (R := ℝ) ![u, w]
    simpa using this
  have hsum := K.finrank_add_finrank_orthogonal
  have h3 : Module.finrank ℝ Vec3 = 3 := by simp [Vec3]
  have hne : Kᗮ ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at hsum
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hvu : inner ℝ u v = 0 :=
    (Submodule.mem_orthogonal K v).mp hv u (Submodule.subset_span ⟨0, rfl⟩)
  have hvw : inner ℝ w v = 0 :=
    (Submodule.mem_orthogonal K v).mp hv w (Submodule.subset_span ⟨1, rfl⟩)
  set ω := ‖v‖⁻¹ • v
  have hω : ‖ω‖ = 1 := by
    simp only [ω, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)
  have hωu : inner ℝ ω u = 0 := by
    simp only [ω, inner_smul_left]
    rw [real_inner_comm, hvu, mul_zero]
  have hωw : inner ℝ ω w = 0 := by
    simp only [ω, inner_smul_left]
    rw [real_inner_comm, hvw, mul_zero]
  obtain ⟨θ, hθ⟩ := (PadenKahan.exists_exp_act_eq_iff hω u w).mpr
    ⟨by rw [hωu, hωw], by simp [Vec3.perp, hωu, hωw, hu, hw]⟩
  exact ⟨Rotation.exp ω θ, hθ⟩

/-- **MLS p. 140: the inverse kinematics of a Stewart leg is solvable for every tool pose.** For a
nondegenerate reference leg (`p ≠ q_s`), every tool pose `g_st` satisfies the leg's structure
equation (3.72) with the extension `θ = ‖q_s - g_st q_t‖ - L` ("we find the locations of the pivot
points and solve for the distance between each base and the appropriate pivot") and suitable
rotations `R_s`, `R_t` of the two spherical joints. -/
theorem exists_legPose_eq (qs qt : Vec3) (g₀ g : RigidTransform) (h : refPivot qt g₀ ≠ qs) :
    ∃ Rs Rt : Rotation,
      legPose qs qt g₀ Rs (‖qs - g.applyPoint qt‖ - ‖refPivot qt g₀ - qs‖) Rt = g := by
  set p := refPivot qt g₀
  set u := legDirection qs qt g₀
  set c := g.applyPoint qt
  set L := ‖p - qs‖
  have hL : L ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  have hpu : p - qs = L • u := by
    simp only [u, legDirection, smul_smul, mul_inv_cancel₀ hL, one_smul, p, L]
  have hu : ‖u‖ = 1 := by
    simp only [u, legDirection, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hL
  -- the current leg direction
  obtain ⟨w, hw, hcw⟩ : ∃ w : Vec3, ‖w‖ = 1 ∧ c - qs = ‖c - qs‖ • w := by
    by_cases hc : c - qs = 0
    · exact ⟨u, hu, by rw [hc, norm_zero, zero_smul]⟩
    · refine ⟨‖c - qs‖⁻¹ • (c - qs), ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc)]
      · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc), one_smul]
  obtain ⟨Rs, hRs⟩ := exists_rotation_act_eq hu hw
  set θ := ‖qs - c‖ - L
  set T := Twist.exp (Twist.prismatic u) θ
  set S := sphericalJoint qs Rs
  set X := T⁻¹ * S⁻¹ * g * g₀⁻¹
  have hXp : X.applyPoint p = p := by
    have hg₀ : g₀⁻¹.applyPoint p = qt := RigidTransform.inv_applyPoint_applyPoint g₀ qt
    have hSf : S.applyPoint (qs + ‖c - qs‖ • u) = c := by
      have h1 : S.applyPoint (qs + ‖c - qs‖ • u) = qs + ‖c - qs‖ • w := by
        simp only [S, sphericalJoint, RigidTransform.applyPoint, map_add, map_smul, hRs]
        abel
      rw [h1, ← hcw]
      abel
    have hS : S⁻¹.applyPoint c = qs + ‖c - qs‖ • u := by
      have := RigidTransform.inv_applyPoint_applyPoint S (qs + ‖c - qs‖ • u)
      rwa [hSf] at this
    have hT : ∀ y, T⁻¹.applyPoint y = y - θ • u := by
      intro y
      simp [T, Twist.exp_prismatic, RigidTransform.applyPoint, sub_eq_add_neg]
    have hp : p = qs + L • u := by rw [← hpu]; abel
    have hθ : θ = ‖c - qs‖ - L := by simp only [θ, norm_sub_rev qs c]
    simp only [X, RigidTransform.mul_applyPoint]
    rw [hg₀, show g.applyPoint qt = c from rfl, hS, hT, hθ, sub_smul]
    conv_rhs => rw [hp]
    abel
  refine ⟨Rs, X.rotation, ?_⟩
  rw [legPose, ← eq_sphericalJoint_of_applyPoint_eq hXp]
  change S * T * X * g₀ = g
  simp only [X]
  group

/-- The seven columns of the Jacobian (3.73) of one Stewart leg, MLS p. 141: the base spherical
joint's `(-eₖ × q_s, eₖ)`, the prismatic `(w, 0)` along the current leg, and the tool spherical
joint's `(-eₖ × c, eₖ)` at the current tool pivot `c`. -/
def legJacobian (qs c w : Vec3) : Fin 7 → Twist :=
  ![Twist.revolute (EuclideanSpace.single 0 1) qs, Twist.revolute (EuclideanSpace.single 1 1) qs,
    Twist.revolute (EuclideanSpace.single 2 1) qs, Twist.prismatic w,
    Twist.revolute (EuclideanSpace.single 0 1) c, Twist.revolute (EuclideanSpace.single 1 1) c,
    Twist.revolute (EuclideanSpace.single 2 1) c]

/-- **MLS p. 141, eq. (3.73), and Exercise 22(b), p. 153: the leg Jacobian is never singular while
the leg length is nonzero.** If the current tool pivot `c` differs from the base pivot `q_s` and
the prismatic direction is `w = a (c - q_s)` with `a ≠ 0`, the seven columns of (3.73) span all
twists: every tool velocity is produced by the leg ("all tool velocities are admissible"). -/
theorem span_legJacobian_eq_top {qs c w : Vec3} (hc : c ≠ qs) {a : ℝ} (ha : a ≠ 0)
    (hw : w = a • (c - qs)) : Submodule.span ℝ (Set.range (legJacobian qs c w)) = ⊤ := by
  set S := Submodule.span ℝ (Set.range (legJacobian qs c w))
  have hcol : ∀ i, legJacobian qs c w i ∈ S := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hrev : ∀ (ω : Vec3) (x : Vec3), (∀ k : Fin 3,
      Twist.revolute (EuclideanSpace.single k 1) x ∈ S) → Twist.revolute ω x ∈ S := by
    intro ω x hx
    rw [revolute_eq_sum_sphericalColumns]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hx k)
  have hqs : ∀ ω, Twist.revolute ω qs ∈ S := fun ω => hrev ω qs fun k => by
    fin_cases k
    · exact hcol 0
    · exact hcol 1
    · exact hcol 2
  have hc' : ∀ ω, Twist.revolute ω c ∈ S := fun ω => hrev ω c fun k => by
    fin_cases k
    · exact hcol 4
    · exact hcol 5
    · exact hcol 6
  set d := c - qs
  have hd : d ≠ 0 := sub_ne_zero.mpr hc
  have hdS : Twist.prismatic d ∈ S := by
    have h3 : Twist.prismatic w ∈ S := hcol 3
    rw [hw, prismatic_smul] at h3
    have := Submodule.smul_mem S a⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
  have hperp : ∀ ω, Twist.prismatic (Vec3.cross ω d) ∈ S := by
    intro ω
    have : Twist.prismatic (Vec3.cross ω d) = Twist.revolute ω qs - Twist.revolute ω c := by
      apply Twist.ext
      · simp only [Twist.prismatic, Twist.revolute, Twist.sub_linear, d]
        rw [sub_eq_add_neg, Vec3.cross_add, Vec3.cross_neg]
        abel
      · simp [Twist.prismatic, Twist.revolute]
    rw [this]
    exact S.sub_mem (hqs ω) (hc' ω)
  have hdd : inner ℝ d d ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)
  have htrans : ∀ t, Twist.prismatic t ∈ S := by
    intro t
    rw [decomp_s d t hdd, prismatic_add, prismatic_smul]
    exact S.add_mem (S.smul_mem _ hdS) (hperp _)
  rw [eq_top_iff]
  rintro ⟨v, ω⟩ -
  have : (⟨v, ω⟩ : Twist) = Twist.revolute ω qs + Twist.prismatic (v + Vec3.cross ω qs) := by
    apply Twist.ext <;> simp [Twist.revolute, Twist.prismatic]
  rw [this]
  exact S.add_mem (hqs ω) (htrans _)

/-- **MLS p. 141: coplanar legs cannot generate a force normal to their plane.** If every leg
direction `wᵢ` is orthogonal to `n ≠ 0`, the force `(n, 0)` is not a combination of the pure
forces `(wᵢ, cᵢ × wᵢ)` transmitted by the actuated prismatic joints through the tool pivots
`cᵢ`, whatever the pivots: "the mechanism cannot resist (or apply) nonplanar forces". -/
theorem normalForce_not_mem_span_legForces {k : ℕ} (n : Vec3) (hn : n ≠ 0) (w c : Fin k → Vec3)
    (hw : ∀ i, inner ℝ n (w i) = 0) :
    (⟨n, 0⟩ : Wrench) ∉ Submodule.span ℝ (Set.range fun i => (⟨w i, Vec3.cross (c i) (w i)⟩ : Wrench)) := by
  intro hmem
  have key : ∀ F ∈ Submodule.span ℝ (Set.range fun i =>
      (⟨w i, Vec3.cross (c i) (w i)⟩ : Wrench)), inner ℝ n F.force = 0 := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hw i
    | zero => simp
    | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
    | smul r x _ hx => simp [inner_smul_right, hx]
  have := key _ hmem
  simp only [real_inner_self_eq_norm_sq] at this
  exact hn (norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this))

/-- **MLS p. 141: coplanar legs cannot generate torques about axes in their plane.** If the leg
directions `wᵢ` and the tool pivots `cᵢ` lie in the plane through the base origin with normal `n`
(`nᵀwᵢ = 0`, `nᵀcᵢ = 0`), no pure torque `(0, τ)` with `τ ≠ 0`, `nᵀτ = 0` is a combination of the
transmitted pure forces `(wᵢ, cᵢ × wᵢ)`. -/
theorem planarTorque_not_mem_span_legForces {k : ℕ} {n : Vec3} (hn : ‖n‖ = 1) (w c : Fin k → Vec3)
    (hw : ∀ i, inner ℝ n (w i) = 0) (hc : ∀ i, inner ℝ n (c i) = 0) {τ : Vec3} (hτ : τ ≠ 0)
    (hτn : inner ℝ n τ = 0) :
    (⟨0, τ⟩ : Wrench) ∉ Submodule.span ℝ (Set.range fun i => (⟨w i, Vec3.cross (c i) (w i)⟩ : Wrench)) := by
  intro hmem
  have key : ∀ F ∈ Submodule.span ℝ (Set.range fun i =>
      (⟨w i, Vec3.cross (c i) (w i)⟩ : Wrench)), inner ℝ τ F.torque = 0 := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      change inner ℝ τ (Vec3.cross (c i) (w i)) = 0
      rw [cross_eq_inner_smul_of_perp_s hn (hc i) (hw i), inner_smul_right, real_inner_comm n τ,
        hτn, mul_zero]
    | zero => simp
    | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
    | smul r x _ hx => simp [inner_smul_right, hx]
  have := key _ hmem
  simp only [real_inner_self_eq_norm_sq] at this
  exact hτ (norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this))

end Stewart

end RoboLean
