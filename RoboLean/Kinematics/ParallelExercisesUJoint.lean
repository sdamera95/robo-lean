import RoboLean.Kinematics.StewartPlatform
import RoboLean.Kinematics.ParallelMechanism

/-!
# The Stewart platform with U-joints: MLS Exercise 22(d)

MLS Chapter 3, Exercise 22(c)–(d), printed p. 153, with the structure equation (3.72) of p. 140
and the rank of the structure equations (3.70) of p. 134. Exercise 22(c) replaces the twelve
spherical joints of the Stewart platform by U-joints ("two orthogonal revolute joints which
intersect at a point"); part (d) asks for the structure equations and whether there are singular
configurations.

* A leg with U-joints is a serial chain of five joints: two revolute joints with axes through the
  base pivot `q_s`, the prismatic joint along the reference leg direction `u` (as in
  `Stewart.legDirection`), and two revolute joints with axes through the reference tool pivot
  `p = g_st(0) q_t`; the structure equation of the leg is (3.72) with the spherical joints replaced
  by the products of the two revolute exponentials.
* Every solution of a leg's structure equation keeps the leg length `‖q_s - g_st q_t‖ = |L + θ₃|`,
  `L = ‖p - q_s‖`, as for spherical joints (`Stewart.norm_sub_legPose_applyPoint`).
* The rank of the structure equations is at most five at every configuration of a U-joint platform
  (each leg's Jacobian has five columns), so no configuration has every tool velocity admissible.
  This answers part (d) in the reading that a configuration is singular when the tool loses a
  direction of instantaneous motion (p. 134): every configuration is singular in that sense, in
  contrast with part (b), where the spherical-joint platform has all tool velocities admissible
  when every leg length is positive (p. 141).

The theorems hold for any unit axes through the pivots; the orthogonality of the two axes of a
U-joint is not used. These are statements about the coordinate model.
-/

noncomputable section

namespace RoboLean

namespace ParallelMechanism

/-- The rank `ρ` of the structure equations (eq. (3.70), MLS p. 134) is at most the number of
joints of any one chain: the admissible velocities lie in the span of that chain's Jacobian
columns. -/
theorem structureRank_le_card {k : ℕ} {n : Fin k → ℕ}
    (P : ParallelMechanism k n) (Θ : (i : Fin k) → Fin (n i) → ℝ) (i : Fin k) :
    P.structureRank Θ ≤ n i := by
  calc P.structureRank Θ ≤
        Module.finrank ℝ (Submodule.span ℝ (Set.range ((P.chain i).spatialJacobian (Θ i)))) :=
      Submodule.finrank_mono (iInf_le _ i)
    _ ≤ Fintype.card (Fin (n i)) := finrank_range_le_card _
    _ = n i := Fintype.card_fin _

end ParallelMechanism

namespace Stewart

/-- **MLS Exercise 22(c)–(d), p. 153: one leg of the Stewart platform with U-joints**, as a serial
chain of five joints: revolute joints about the axes `a`, `b` through the base pivot `q_s`, the
prismatic joint along the reference leg direction `legDirection q_s q_t g₀`, and revolute joints
about the axes `c`, `e` through the reference tool pivot `refPivot q_t g₀ = g₀ q_t`; reference tool
pose `g₀ = g_st(0)`. Twists `(-ω × q, ω)` and `(u, 0)`, order `(v, ω)`. -/
def uJointLeg (qs qt a b c e : Vec3) (g₀ : RigidTransform) : SerialChain 5 where
  twist := ![Twist.revolute a qs, Twist.revolute b qs, Twist.prismatic (legDirection qs qt g₀),
    Twist.revolute c (refPivot qt g₀), Twist.revolute e (refPivot qt g₀)]
  toolRef := g₀

/-- **MLS Exercise 22(d), p. 153, with eq. (3.72), p. 140: the structure equation of a U-joint
leg.** The leg's forward kinematics is
`e^{ξ̂_a θ₁} e^{ξ̂_b θ₂} e^{ξ̂ θ₃} e^{ξ̂_c θ₄} e^{ξ̂_e θ₅} g_st(0)`: the base U-joint, the prismatic
joint and the tool U-joint in place of the spherical joints `g_s(R_s)` and `g_t(R_t)`. -/
theorem uJointLeg_fk (qs qt a b c e : Vec3) (g₀ : RigidTransform) (θ : Fin 5 → ℝ) :
    (uJointLeg qs qt a b c e g₀).fk θ =
      Twist.exp (Twist.revolute a qs) (θ 0) * Twist.exp (Twist.revolute b qs) (θ 1) *
        Twist.exp (Twist.prismatic (legDirection qs qt g₀)) (θ 2) *
          Twist.exp (Twist.revolute c (refPivot qt g₀)) (θ 3) *
            Twist.exp (Twist.revolute e (refPivot qt g₀)) (θ 4) * g₀ := by
  simp only [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
    List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

/-- **MLS Exercise 22(d), p. 153, with p. 140: the leg length of a U-joint leg.** For unit axes and
a nondegenerate reference leg (`p ≠ q_s`), every configuration of the leg puts the pivots at
distance `‖q_s - g q_t‖ = |L + θ₃|`, `L = ‖p - q_s‖`, `θ₃` the prismatic coordinate. -/
theorem norm_sub_uJointLeg_fk_applyPoint {qs qt a b c e : Vec3} {g₀ : RigidTransform}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (he : ‖e‖ = 1) (h : refPivot qt g₀ ≠ qs)
    (θ : Fin 5 → ℝ) :
    ‖qs - ((uJointLeg qs qt a b c e g₀).fk θ).applyPoint qt‖ = |‖refPivot qt g₀ - qs‖ + θ 2| := by
  set p := refPivot qt g₀
  set u := legDirection qs qt g₀
  have hL : ‖p - qs‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  have hpu : p - qs = ‖p - qs‖ • u := by
    simp only [u, legDirection, smul_smul, mul_inv_cancel₀ hL, one_smul, p]
  have hu : ‖u‖ = 1 := by
    simp only [u, legDirection, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hL, p]
  have hp : ∀ ω : Vec3, p ∈ axisLine p ω := fun ω =>
    (mem_axisLine_iff p ω p).2 ⟨0, by rw [zero_smul, add_zero]⟩
  rw [uJointLeg_fk]
  simp only [RigidTransform.mul_applyPoint]
  rw [show g₀.applyPoint qt = p from rfl,
    Twist.exp_revolute_applyPoint_of_mem_axisLine e p he _ (hp e),
    Twist.exp_revolute_applyPoint_of_mem_axisLine c p hc _ (hp c), Twist.exp_prismatic,
    Twist.exp_revolute_applyPoint b qs hb, Twist.exp_revolute_applyPoint a qs ha]
  have hT : (⟨1, θ 2 • u⟩ : RigidTransform).applyPoint p = p + θ 2 • u := by
    simp [RigidTransform.applyPoint]
  rw [hT, add_sub_cancel_right, sub_add_cancel_right, norm_neg, Rotation.norm_act,
    Rotation.norm_act, add_sub_right_comm]
  conv_lhs => rw [hpu]
  rw [← add_smul, norm_smul, hu, mul_one, Real.norm_eq_abs]

/-- **MLS Exercise 22(c)–(d), p. 153: the Stewart platform with U-joints** as a parallel mechanism
(§5.2, p. 132) with six legs `uJointLeg`: base pivots `q_s i`, tool pivots `q_t i` in the tool
frame, U-joint axes `a i, b i` at the base and `c i, e i` at the tool, one reference tool pose
`g₀`. -/
def uJointStewartPlatform (qs qt a b c e : Fin 6 → Vec3) (g₀ : RigidTransform) :
    ParallelMechanism 6 (fun _ => 5) where
  chain i := uJointLeg (qs i) (qt i) (a i) (b i) (c i) (e i) g₀

/-- **MLS Exercise 22(d), p. 153: the rank of the structure equations of the U-joint platform** is
at most five at every configuration (eq. (3.70), p. 134). -/
theorem uJointStewartPlatform_structureRank_le (qs qt a b c e : Fin 6 → Vec3)
    (g₀ : RigidTransform) (Θ : Fin 6 → Fin 5 → ℝ) :
    (uJointStewartPlatform qs qt a b c e g₀).structureRank Θ ≤ 5 := by
  exact ParallelMechanism.structureRank_le_card _ Θ 0

/-- **MLS Exercise 22(d), p. 153: no configuration of the U-joint platform has every tool velocity
admissible** (p. 134: the tool cannot move instantaneously in some direction), in contrast with
the spherical-joint platform of p. 141 and Exercise 22(b). -/
theorem uJointStewartPlatform_exists_not_mem_admissibleVelocities (qs qt a b c e : Fin 6 → Vec3)
    (g₀ : RigidTransform) (Θ : Fin 6 → Fin 5 → ℝ) :
    ∃ V : Twist, V ∉ (uJointStewartPlatform qs qt a b c e g₀).admissibleVelocities Θ := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  have htop : (uJointStewartPlatform qs qt a b c e g₀).admissibleVelocities Θ = ⊤ :=
    Submodule.eq_top_iff'.2 hall
  have h6 := ((uJointStewartPlatform qs qt a b c e g₀).admissibleVelocities_eq_top_iff Θ).1 htop
  have h5 := uJointStewartPlatform_structureRank_le qs qt a b c e g₀ Θ
  omega

end Stewart

end RoboLean
