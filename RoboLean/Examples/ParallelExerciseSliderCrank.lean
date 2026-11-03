import RoboLean.Kinematics.ParallelMechanism
import RoboLean.Examples.RigidTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The slider–crank of MLS Exercise 20, parts (b)–(e)

MLS Chapter 3, Exercise 20, printed pp. 151–152 (figure on p. 152), with the definitions of
§5.2, pp. 132–135. The slider–crank is modelled as a `ParallelMechanism` with two chains from the
base frame `S` (at the crank pivot) to the tool frame `T` (on the slider block):

* chain `0`, the linkage: three revolute joints about `+z` through `(0, 0, 0)`, `(l₁, 0, 0)` and
  `(l₁ + l₂, 0, 0)`, with the reference tool pose `g_st(0) = (I, (l₁ + l₂ + l₃, 0, 0))`; its zero
  configuration is the linkage stretched along the slide line, and its joint angles are the
  figure's `θ₁` (crank from the slide line), `θ₂` (rod from the crank's extension) and `θ₃` (slider
  bar from the rod's extension), all measured counterclockwise;
* chain `1`, the slide: one prismatic joint along `+x` with `g_st(0) = I`, so that its joint
  coordinate is the figure's `d`, the distance from `S` to `T` along the slide line.

The figure draws the slide line through the crank pivot `S` (an in-line slider–crank) and the
bar `l₃` rigid with the slider block. With the counterclockwise convention the angle `θ₂` of the
drawn configuration is negative; the figure's arc for `θ₂` is drawn clockwise.

Contents:

* (b) the structure equations: the loop closes exactly when `θ₁ + θ₂ + θ₃ ∈ 2πℤ`,
  `l₁ sin θ₁ + l₂ sin(θ₁ + θ₂) = 0` and `d = l₁ cos θ₁ + l₂ cos(θ₁ + θ₂) + l₃`;
* (c) the instantaneous joint twists (the columns of the two spatial Jacobians), in the order
  `(v, ω)`: the revolute twists about `+z` through the current joint positions, and `(e₁, 0)`;
* (d) with `d` active: for positive `l₁ ≠ l₂` the rank `ρ` of the structure equations is `0` at the
  configurations with `sin θ₁ = 0` (the crank on the slide line, the dead centres) and `1`
  elsewhere, so the kinematic singularities are exactly the dead centres; the slide alone
  transmits every wrench, so there is no actuator singularity;
* (e) with `θ₁` active: the mechanism is actuator singular exactly when `cos(θ₁ + θ₂) = 0`, the rod
  perpendicular to the slide; for positive `l₁, l₂` such configurations satisfy the structure
  equations for some `θ, d` exactly when `l₂ ≤ l₁`, whatever `l₃`.

The case `l₁ = l₂` is excluded from (d): the folded configurations then put the third joint on
the crank pivot and the rank there depends on more than `sin θ₁`. These are statements about the
coordinate model, not about a physical mechanism.
-/

noncomputable section

open Real

namespace RoboLean

namespace Examples

/-! ### Private coordinate helpers -/

private theorem scr_norm_zAxis : ‖Rotation.zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [Rotation.zAxis, Fin.sum_univ_succ]

private theorem scr_zRotation_act (t x y z : ℝ) :
    (Rotation.zRotation t).act (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z := by
  ext i
  fin_cases i <;>
    simp [Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, vec]
  all_goals ring

private theorem scr_vec_eq {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    vec a b c = vec a' b' c' := by
  rw [ha, hb, hc]

private theorem scr_exp_z_applyPoint (qx qy qz t x y z : ℝ) :
    (Twist.exp (Twist.revolute Rotation.zAxis (vec qx qy qz)) t).applyPoint (vec x y z) =
      vec (cos t * (x - qx) - sin t * (y - qy) + qx)
        (sin t * (x - qx) + cos t * (y - qy) + qy) z := by
  rw [Twist.exp_revolute_applyPoint _ _ scr_norm_zAxis]
  have : vec x y z - vec qx qy qz = vec (x - qx) (y - qy) (z - qz) := by
    ext i
    fin_cases i <;> simp [vec]
  rw [this, show Rotation.exp Rotation.zAxis t = Rotation.zRotation t from rfl, scr_zRotation_act]
  ext i
  fin_cases i <;> simp [vec]

private theorem scr_exp_z_applyVector (q : Vec3) (t : ℝ) :
    (Twist.exp (Twist.revolute Rotation.zAxis q) t).applyVector Rotation.zAxis =
      Rotation.zAxis := by
  simp only [RigidTransform.applyVector, Twist.exp_rotation, Twist.revolute]
  exact Rotation.exp_act_unit_axis _ scr_norm_zAxis t

private theorem scr_translation (g : RigidTransform) :
    g.translation = g.applyPoint (vec 0 0 0) := by
  have : vec 0 0 0 = 0 := by
    ext i
    fin_cases i <;> rfl
  simp [RigidTransform.applyPoint, this]

private theorem scr_vec_eq_iff (a b c a' b' c' : ℝ) :
    vec a b c = vec a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    have h0 := congrArg (fun v : Vec3 => v 0) h
    have h1 := congrArg (fun v : Vec3 => v 1) h
    have h2 := congrArg (fun v : Vec3 => v 2) h
    simp only [vec, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private theorem scr_revolute_z (x y z : ℝ) :
    Twist.revolute Rotation.zAxis (vec x y z) = ⟨vec y (-x) 0, vec 0 0 1⟩ := by
  apply Twist.ext <;> ext i <;> fin_cases i <;>
    simp [Twist.revolute, Vec3.cross, cross_apply, Rotation.zAxis, vec]

private theorem scr_sin_int_mul_two_pi (k : ℤ) : sin (k * (2 * π)) = 0 := by
  rw [show (k : ℝ) * (2 * π) = ((2 * k : ℤ) : ℝ) * π by push_cast; ring]
  exact sin_int_mul_pi _

private theorem scr_zRotation_eq_one_iff (a : ℝ) :
    Rotation.zRotation a = 1 ↔ ∃ k : ℤ, a = k * (2 * π) := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    rw [Rotation.zRotation_val] at hv
    have hc := congrFun (congrFun hv 0) 0
    have hs := congrFun (congrFun hv 1) 0
    simp at hc hs
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp
      (Real.Angle.cos_sin_inj (hc.trans cos_zero.symm) (hs.trans sin_zero.symm))
    exact ⟨k, by linarith⟩
  · rintro ⟨k, rfl⟩
    have := Rotation.exp_add_int_mul_two_pi _ scr_norm_zAxis 0 k
    rw [zero_add, Rotation.exp_zero] at this
    exact this

/-- The linkage chain of the slider–crank of MLS Exercise 20 (figure, p. 152): revolute joints
about `+z` through `(0, 0, 0)`, `(l₁, 0, 0)` and `(l₁ + l₂, 0, 0)` (twists `(-ω × q, ω)`, order
`(v, ω)`), and the reference tool pose `(I, (l₁ + l₂ + l₃, 0, 0))`: the zero configuration
stretches the crank, the rod and the slider bar along the slide line, angles counterclockwise. -/
def sliderCrankLinkage (l₁ l₂ l₃ : ℝ) : SerialChain 3 where
  twist := ![Twist.revolute Rotation.zAxis (vec 0 0 0), Twist.revolute Rotation.zAxis (vec l₁ 0 0),
    Twist.revolute Rotation.zAxis (vec (l₁ + l₂) 0 0)]
  toolRef := ⟨1, vec (l₁ + l₂ + l₃) 0 0⟩

/-- The slide chain of the slider–crank of MLS Exercise 20 (figure, p. 152): one prismatic joint
along `+x` (twist `(e₁, 0)`, order `(v, ω)`) with reference tool pose `I`, so that the joint
coordinate is the figure's distance `d` from `S` to `T`. -/
def sliderCrankSlide : SerialChain 1 where
  twist := ![Twist.prismatic (vec 1 0 0)]
  toolRef := 1

/-- **MLS Exercise 20, p. 152: the slider–crank as a parallel mechanism** (§5.2, p. 132), chain
`0` the linkage `sliderCrankLinkage` and chain `1` the slide `sliderCrankSlide`, one base frame
at the crank pivot and one tool frame on the slider block. -/
def sliderCrank (l₁ l₂ l₃ : ℝ) : ParallelMechanism 2 ![3, 1] :=
  ParallelMechanism.ofClosedChain ⟨sliderCrankLinkage l₁ l₂ l₃, sliderCrankSlide⟩

/-- A configuration of the slider–crank of MLS Exercise 20 (p. 152) from the linkage angles
`θ = (θ₁, θ₂, θ₃)` and the slide coordinate `d`; every configuration is of this form
(`ParallelMechanism.pairEquiv`). -/
def sliderCrankConfig (θ : Fin 3 → ℝ) (d : ℝ) : (i : Fin 2) → Fin (![3, 1] i) → ℝ :=
  (ParallelMechanism.pairEquiv 3 1).symm (θ, ![d])

/-- The slide coordinate `d` actuated, MLS Exercise 20(d), p. 152: no joint of the linkage, the
joint of the slide (actuated sets in the sense of `ParallelMechanism.transmissibleWrenches`). -/
def sliderCrankSlideActuated : (i : Fin 2) → Set (Fin (![3, 1] i)) :=
  fun i => {_j | (i : ℕ) = 1}

/-- The crank angle `θ₁` actuated, MLS Exercise 20(e), p. 152: the first joint of the linkage
and no joint of the slide (actuated sets in the sense of
`ParallelMechanism.transmissibleWrenches`). -/
def sliderCrankCrankActuated : (i : Fin 2) → Set (Fin (![3, 1] i)) :=
  fun i => {j | (i : ℕ) = 0 ∧ (j : ℕ) = 0}

/-- **MLS Exercise 20(b), p. 152: forward kinematics of the linkage** by the product of
exponentials (eq. (3.3), p. 87): `g(θ) = (Rz(θ₁ + θ₂ + θ₃), (l₁c₁ + l₂c₁₂ + l₃c₁₂₃,
l₁s₁ + l₂s₁₂ + l₃s₁₂₃, 0))`, angles counterclockwise from the slide line. -/
theorem sliderCrankLinkage_fk (l₁ l₂ l₃ : ℝ) (θ : Fin 3 → ℝ) :
    (sliderCrankLinkage l₁ l₂ l₃).fk θ =
      ⟨Rotation.zRotation (θ 0 + θ 1 + θ 2),
        vec (l₁ * cos (θ 0) + l₂ * cos (θ 0 + θ 1) + l₃ * cos (θ 0 + θ 1 + θ 2))
          (l₁ * sin (θ 0) + l₂ * sin (θ 0 + θ 1) + l₃ * sin (θ 0 + θ 1 + θ 2)) 0⟩ := by
  have hfk : (sliderCrankLinkage l₁ l₂ l₃).fk θ =
      Twist.exp (Twist.revolute Rotation.zAxis (vec 0 0 0)) (θ 0) *
        (Twist.exp (Twist.revolute Rotation.zAxis (vec l₁ 0 0)) (θ 1) *
          (Twist.exp (Twist.revolute Rotation.zAxis (vec (l₁ + l₂) 0 0)) (θ 2) * 1)) *
        ⟨1, vec (l₁ + l₂ + l₃) 0 0⟩ := by
    simp only [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
      List.ofFn_zero, List.prod_cons, List.prod_nil]
    rfl
  apply RigidTransform.ext
  · rw [hfk]
    simp only [RigidTransform.mul_rotation, Twist.exp_rotation, Twist.revolute, mul_one]
    simp only [Rotation.zRotation]
    rw [Rotation.exp_add, Rotation.exp_add, mul_assoc]
  · rw [scr_translation, hfk]
    simp only [RigidTransform.mul_applyPoint, RigidTransform.one_applyPoint]
    rw [show (⟨1, vec (l₁ + l₂ + l₃) 0 0⟩ : RigidTransform).applyPoint (vec 0 0 0) =
        vec (l₁ + l₂ + l₃) 0 0 from by
      ext i
      fin_cases i <;> simp [RigidTransform.applyPoint, vec]]
    rw [scr_exp_z_applyPoint, scr_exp_z_applyPoint, scr_exp_z_applyPoint]
    apply scr_vec_eq
    · simp only [sin_add, cos_add]
      ring
    · simp only [sin_add, cos_add]
      ring
    · rfl

/-- **MLS Exercise 20(b), p. 152: forward kinematics of the slide**, the translation by `d`
along the slide line, `g(d) = (I, (d, 0, 0))`. -/
theorem sliderCrankSlide_fk (d : Fin 1 → ℝ) : sliderCrankSlide.fk d = ⟨1, vec (d 0) 0 0⟩ := by
  have hfk : sliderCrankSlide.fk d = Twist.exp (Twist.prismatic (vec 1 0 0)) (d 0) * 1 * 1 := by
    simp only [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
      List.ofFn_zero, List.prod_cons, List.prod_nil]
    rfl
  rw [hfk, Twist.exp_prismatic, mul_one, mul_one]
  congr 1
  ext i
  fin_cases i <;> simp [vec]

/-- **MLS Exercise 20(b), p. 152: the structure equations** (eq. (3.65), p. 132). A configuration
lies in the joint space `Q′` exactly when `θ₁ + θ₂ + θ₃` is a multiple of `2π`,
`l₁ sin θ₁ + l₂ sin(θ₁ + θ₂) = 0` and `d = l₁ cos θ₁ + l₂ cos(θ₁ + θ₂) + l₃`. -/
theorem sliderCrank_mem_admissible_iff (l₁ l₂ l₃ : ℝ) (θ : Fin 3 → ℝ) (d : ℝ) :
    sliderCrankConfig θ d ∈ (sliderCrank l₁ l₂ l₃).admissible ↔
      (∃ k : ℤ, θ 0 + θ 1 + θ 2 = k * (2 * π)) ∧ l₁ * sin (θ 0) + l₂ * sin (θ 0 + θ 1) = 0 ∧
        d = l₁ * cos (θ 0) + l₂ * cos (θ 0 + θ 1) + l₃ := by
  rw [sliderCrank, ParallelMechanism.mem_admissible_ofClosedChain_iff, sliderCrankConfig,
    Equiv.apply_symm_apply, ClosedChain.mem_admissible_iff]
  simp only [sliderCrankLinkage_fk, sliderCrankSlide_fk, Matrix.cons_val_zero]
  constructor
  · rintro ⟨-, -, hfk⟩
    obtain ⟨hR, hp⟩ := RigidTransform.mk.inj hfk
    obtain ⟨k, hk⟩ := (scr_zRotation_eq_one_iff _).1 hR
    obtain ⟨h0, h1, -⟩ := (scr_vec_eq_iff _ _ _ _ _ _).1 hp
    rw [hk, cos_int_mul_two_pi, mul_one] at h0
    rw [hk, scr_sin_int_mul_two_pi, mul_zero, add_zero] at h1
    exact ⟨⟨k, hk⟩, h1, h0.symm⟩
  · rintro ⟨⟨k, hk⟩, hs, hd⟩
    refine ⟨trivial, trivial, ?_⟩
    rw [(scr_zRotation_eq_one_iff _).2 ⟨k, hk⟩, hk, cos_int_mul_two_pi, scr_sin_int_mul_two_pi]
    congr 1
    apply scr_vec_eq
    · rw [hd]
      ring
    · rw [mul_zero, add_zero, hs]
    · rfl

/-- **MLS Exercise 20(c), p. 152: the instantaneous twists of the linkage** (eq. (3.54), p. 116),
order `(v, ω)`: `ξ₁′ = (0, 0, 0, 0, 0, 1)`, `ξ₂′ = (l₁s₁, -l₁c₁, 0, 0, 0, 1)` and
`ξ₃′ = (l₁s₁ + l₂s₁₂, -(l₁c₁ + l₂c₁₂), 0, 0, 0, 1)`, the revolute twists about `+z` through the
crank pivot, the crank pin and the slider pin (planar form `(q_y, -q_x, 1)` of p. 136). -/
theorem sliderCrankLinkage_spatialJacobian (l₁ l₂ l₃ : ℝ) (θ : Fin 3 → ℝ) :
    (sliderCrankLinkage l₁ l₂ l₃).spatialJacobian θ =
      ![⟨vec 0 0 0, vec 0 0 1⟩, ⟨vec (l₁ * sin (θ 0)) (-(l₁ * cos (θ 0))) 0, vec 0 0 1⟩,
        ⟨vec (l₁ * sin (θ 0) + l₂ * sin (θ 0 + θ 1)) (-(l₁ * cos (θ 0) + l₂ * cos (θ 0 + θ 1))) 0,
          vec 0 0 1⟩] := by
  funext i
  fin_cases i
  · show (sliderCrankLinkage l₁ l₂ l₃).spatialJacobian θ 0 = ⟨vec 0 0 0, vec 0 0 1⟩
    rw [SerialChain.spatialJacobian_zero]
    change Twist.revolute Rotation.zAxis (vec 0 0 0) = _
    rw [scr_revolute_z]
    simp
  · change Twist.adjoint (((sliderCrankLinkage l₁ l₂ l₃).jointMotions θ).take 1).prod
      (Twist.revolute Rotation.zAxis (vec l₁ 0 0)) = _
    have hg : ((sliderCrankLinkage l₁ l₂ l₃).jointMotions θ).take 1 =
        [Twist.exp (Twist.revolute Rotation.zAxis (vec 0 0 0)) (θ 0)] := by
      simp [SerialChain.jointMotions, List.ofFn_succ, sliderCrankLinkage]
    rw [hg, List.prod_singleton, Twist.adjoint_revolute, scr_exp_z_applyVector,
      scr_exp_z_applyPoint, scr_revolute_z]
    congr 1
    apply scr_vec_eq <;> ring
  · change Twist.adjoint (((sliderCrankLinkage l₁ l₂ l₃).jointMotions θ).take 2).prod
      (Twist.revolute Rotation.zAxis (vec (l₁ + l₂) 0 0)) = _
    have hg : ((sliderCrankLinkage l₁ l₂ l₃).jointMotions θ).take 2 =
        [Twist.exp (Twist.revolute Rotation.zAxis (vec 0 0 0)) (θ 0),
          Twist.exp (Twist.revolute Rotation.zAxis (vec l₁ 0 0)) (θ 1)] := by
      simp [SerialChain.jointMotions, List.ofFn_succ, sliderCrankLinkage]
    rw [hg, List.prod_cons, List.prod_singleton, Twist.adjoint_revolute,
      RigidTransform.mul_applyVector, scr_exp_z_applyVector, scr_exp_z_applyVector,
      RigidTransform.mul_applyPoint, scr_exp_z_applyPoint, scr_exp_z_applyPoint, scr_revolute_z]
    congr 1
    apply scr_vec_eq
    · simp only [sin_add]
      ring
    · simp only [cos_add]
      ring
    · rfl

/-- **MLS Exercise 20(c), p. 152: the instantaneous twist of the slide** (eq. (3.54), p. 116),
`(1, 0, 0, 0, 0, 0)` in the order `(v, ω)` at every configuration. -/
theorem sliderCrankSlide_spatialJacobian (d : Fin 1 → ℝ) :
    sliderCrankSlide.spatialJacobian d = ![⟨vec 1 0 0, vec 0 0 0⟩] := by
  funext i
  fin_cases i
  show sliderCrankSlide.spatialJacobian d 0 = ⟨vec 1 0 0, vec 0 0 0⟩
  rw [SerialChain.spatialJacobian_zero]
  change Twist.prismatic (vec 1 0 0) = _
  apply Twist.ext
  · rfl
  · ext i
    fin_cases i <;> simp [Twist.prismatic, vec]

/-! ### The rank of the structure equations -/

private theorem scr_ex_ne_zero : (⟨vec 1 0 0, vec 0 0 0⟩ : Twist) ≠ 0 := by
  intro h
  have := congrArg (fun V : Twist => V.linear 0) h
  simp [vec] at this

private theorem scr_admissibleVelocities (l₁ l₂ l₃ : ℝ) (θ : Fin 3 → ℝ) (d : ℝ) :
    (sliderCrank l₁ l₂ l₃).admissibleVelocities (sliderCrankConfig θ d) =
      Submodule.span ℝ (Set.range ((sliderCrankLinkage l₁ l₂ l₃).spatialJacobian θ)) ⊓
        Submodule.span ℝ {(⟨vec 1 0 0, vec 0 0 0⟩ : Twist)} := by
  ext V
  rw [ParallelMechanism.mem_admissibleVelocities_iff, Fin.forall_fin_two, Submodule.mem_inf,
    Submodule.mem_span_range_iff_exists_fun, Submodule.mem_span_singleton]
  apply and_congr Iff.rfl
  change (∃ g : Fin 1 → ℝ, ∑ l, g l • sliderCrankSlide.spatialJacobian ![d] l = V) ↔ _
  rw [sliderCrankSlide_spatialJacobian]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g 0, by simpa using hg⟩
  · rintro ⟨a, ha⟩
    exact ⟨fun _ => a, by simpa using ha⟩

private theorem scr_finrank_inf_of_mem (W : Submodule ℝ Twist) {x : Twist} (hx : x ≠ 0)
    (h : x ∈ W) : Module.finrank ℝ ↥(W ⊓ Submodule.span ℝ {x}) = 1 := by
  rw [inf_eq_right.2 ((Submodule.span_singleton_le_iff_mem x W).2 h), finrank_span_singleton hx]

private theorem scr_inf_eq_bot_of_not_mem (W : Submodule ℝ Twist) {x : Twist} (h : x ∉ W) :
    W ⊓ Submodule.span ℝ {x} = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyW, hyx⟩ := Submodule.mem_inf.1 hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hyx
  rw [Submodule.mem_bot]
  by_cases hc : c = 0
  · rw [hc, zero_smul]
  · exact absurd (by simpa [smul_smul, inv_mul_cancel₀ hc] using W.smul_mem c⁻¹ hyW) h

private theorem scr_x_ne_zero {l₁ l₂ : ℝ} (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (hne : l₁ ≠ l₂)
    {θ : Fin 3 → ℝ} (hs : l₁ * sin (θ 0) + l₂ * sin (θ 0 + θ 1) = 0) :
    l₁ * cos (θ 0) + l₂ * cos (θ 0 + θ 1) ≠ 0 := by
  intro hX
  have h1 := sin_sq_add_cos_sq (θ 0)
  have h2 := sin_sq_add_cos_sq (θ 0 + θ 1)
  have hsq : (l₁ - l₂) * (l₁ + l₂) = 0 := by
    linear_combination (l₁ * sin (θ 0) - l₂ * sin (θ 0 + θ 1)) * hs +
      (l₁ * cos (θ 0) - l₂ * cos (θ 0 + θ 1)) * hX - l₁ ^ 2 * h1 + l₂ ^ 2 * h2
  rcases mul_eq_zero.1 hsq with h | h
  · exact hne (by linarith)
  · linarith

private theorem scr_ex_mem_span_iff {l₁ l₂ : ℝ} (l₃ : ℝ) (hl₁ : 0 < l₁) (hl₂ : 0 < l₂)
    (hne : l₁ ≠ l₂) {θ : Fin 3 → ℝ} (hs : l₁ * sin (θ 0) + l₂ * sin (θ 0 + θ 1) = 0) :
    (⟨vec 1 0 0, vec 0 0 0⟩ : Twist) ∈
        Submodule.span ℝ (Set.range ((sliderCrankLinkage l₁ l₂ l₃).spatialJacobian θ)) ↔
      sin (θ 0) ≠ 0 := by
  rw [Submodule.mem_span_range_iff_exists_fun, sliderCrankLinkage_spatialJacobian]
  constructor
  · rintro ⟨c, hc⟩ h0
    have hx := congrArg (fun V : Twist => V.linear 0) hc
    simp [Fin.sum_univ_three, vec] at hx
    have : (1 : ℝ) = 0 := by
      linear_combination -hx + (c 1 * l₁) * h0 + c 2 * hs
    exact one_ne_zero this
  · intro h0
    have hX := scr_x_ne_zero hl₁ hl₂ hne hs
    set X := l₁ * cos (θ 0) + l₂ * cos (θ 0 + θ 1) with hXdef
    refine ⟨![-(1 / (l₁ * sin (θ 0))) + cos (θ 0) / (sin (θ 0) * X), 1 / (l₁ * sin (θ 0)),
      -(cos (θ 0) / (sin (θ 0) * X))], ?_⟩
    have hl₁' : l₁ ≠ 0 := hl₁.ne'
    apply Twist.ext <;> ext j <;> fin_cases j <;> simp [Fin.sum_univ_three, vec]
    · field_simp
      linear_combination (-cos (θ 0)) * hs
    · field_simp
      ring

/-- **MLS Exercise 20(d), p. 152, with eq. (3.70), p. 134: the rank of the structure equations.**
For positive `l₁ ≠ l₂` and a configuration of `Q′`, `ρ = 0` when `sin θ₁ = 0` (the crank on the
slide line) and `ρ = 1` otherwise. -/
theorem sliderCrank_structureRank {l₁ l₂ : ℝ} (l₃ : ℝ) (hl₁ : 0 < l₁) (hl₂ : 0 < l₂)
    (hne : l₁ ≠ l₂) {θ : Fin 3 → ℝ} {d : ℝ}
    (h : sliderCrankConfig θ d ∈ (sliderCrank l₁ l₂ l₃).admissible) :
    (sliderCrank l₁ l₂ l₃).structureRank (sliderCrankConfig θ d) =
      if sin (θ 0) = 0 then 0 else 1 := by
  have hs := ((sliderCrank_mem_admissible_iff l₁ l₂ l₃ θ d).1 h).2.1
  rw [ParallelMechanism.structureRank, scr_admissibleVelocities]
  by_cases h0 : sin (θ 0) = 0
  · simp only [h0, ↓reduceIte]
    rw [scr_inf_eq_bot_of_not_mem _
      (fun hm => (scr_ex_mem_span_iff l₃ hl₁ hl₂ hne hs).1 hm h0), finrank_bot]
  · simp only [h0, ↓reduceIte]
    rw [scr_finrank_inf_of_mem _ scr_ex_ne_zero
      ((scr_ex_mem_span_iff l₃ hl₁ hl₂ hne hs).2 h0)]

private theorem scr_structureRank_le_one (l₁ l₂ l₃ : ℝ) (Θ : (i : Fin 2) → Fin (![3, 1] i) → ℝ) :
    (sliderCrank l₁ l₂ l₃).structureRank Θ ≤ 1 := by
  obtain ⟨θ, d, rfl⟩ : ∃ (θ : Fin 3 → ℝ) (d : ℝ), sliderCrankConfig θ d = Θ := by
    refine ⟨fun j => Θ 0 j, Θ 1 ⟨0, Nat.one_pos⟩, ?_⟩
    apply (ParallelMechanism.pairEquiv 3 1).injective
    simp only [sliderCrankConfig, Equiv.apply_symm_apply]
    refine Prod.ext rfl ?_
    funext j
    fin_cases j
    rfl
  rw [ParallelMechanism.structureRank, scr_admissibleVelocities]
  calc Module.finrank ℝ ↥(Submodule.span ℝ (Set.range
          ((sliderCrankLinkage l₁ l₂ l₃).spatialJacobian θ)) ⊓
        Submodule.span ℝ {(⟨vec 1 0 0, vec 0 0 0⟩ : Twist)})
      ≤ Module.finrank ℝ ↥(Submodule.span ℝ {(⟨vec 1 0 0, vec 0 0 0⟩ : Twist)}) :=
        Submodule.finrank_mono inf_le_right
    _ = 1 := finrank_span_singleton scr_ex_ne_zero

/-- **MLS Exercise 20(d), p. 152: the kinematic singularities** (p. 134, the rank of the structure
equations drops, in the convention of `ParallelMechanism.IsKinematicallySingular`). For positive
`l₁ ≠ l₂`, a configuration of `Q′` is kinematically singular exactly when `sin θ₁ = 0`: the crank
and the rod lie on the slide line (the dead centres). -/
theorem sliderCrank_isKinematicallySingular_iff {l₁ l₂ : ℝ} (l₃ : ℝ) (hl₁ : 0 < l₁)
    (hl₂ : 0 < l₂) (hne : l₁ ≠ l₂) {θ : Fin 3 → ℝ} {d : ℝ}
    (h : sliderCrankConfig θ d ∈ (sliderCrank l₁ l₂ l₃).admissible) :
    (sliderCrank l₁ l₂ l₃).IsKinematicallySingular (sliderCrankConfig θ d) ↔ sin (θ 0) = 0 := by
  have hrank := sliderCrank_structureRank l₃ hl₁ hl₂ hne h
  constructor
  · intro hsing
    by_contra h0
    simp only [h0, ↓reduceIte] at hrank
    obtain ⟨Θ₁, -, -, hlt⟩ := hsing Set.univ Filter.univ_mem
    have := scr_structureRank_le_one l₁ l₂ l₃ Θ₁
    omega
  · intro h0
    simp only [h0, ↓reduceIte] at hrank
    obtain ⟨⟨k, hk⟩, hs, hd⟩ := (sliderCrank_mem_admissible_iff l₁ l₂ l₃ θ d).1 h
    have hsa : sin (θ 0 + θ 1) = 0 := by
      rw [h0, mul_zero, zero_add] at hs
      exact (mul_eq_zero.1 hs).resolve_left hl₂.ne'
    have hc0 : cos (θ 0) ^ 2 = 1 := by nlinarith [sin_sq_add_cos_sq (θ 0)]
    have hca : cos (θ 0 + θ 1) ^ 2 = 1 := by nlinarith [sin_sq_add_cos_sq (θ 0 + θ 1)]
    set a := θ 0 + θ 1 with ha
    let δ : ℝ → ℝ := fun ε => arcsin (-(l₁ / l₂) * cos (θ 0) * cos a * sin ε)
    let θε : ℝ → Fin 3 → ℝ := fun ε => ![θ 0 + ε, θ 1 + δ ε - ε, θ 2 - δ ε]
    let dε : ℝ → ℝ := fun ε => l₁ * cos (θ 0 + ε) + l₂ * cos (a + δ ε) + l₃
    let F : ℝ → (i : Fin 2) → Fin (![3, 1] i) → ℝ := fun ε => sliderCrankConfig (θε ε) (dε ε)
    have hδ0 : δ 0 = 0 := by simp [δ]
    have hF0 : F 0 = sliderCrankConfig θ d := by
      simp only [F]
      congr 1
      · funext j
        fin_cases j <;> simp [θε, hδ0]
      · simp only [dε, hδ0, add_zero, hd, ha]
    have hδc : Continuous δ := by
      simp only [δ]
      exact continuous_arcsin.comp (continuous_const.mul continuous_sin)
    have hFc : Continuous F := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      fin_cases i
      · fin_cases j
        · exact continuous_const.add continuous_id
        · exact (continuous_const.add hδc).sub continuous_id
        · exact continuous_const.sub hδc
      · fin_cases j
        exact ((continuous_const.mul (continuous_cos.comp (continuous_const.add continuous_id))).add
          (continuous_const.mul (continuous_cos.comp (continuous_const.add hδc)))).add
            continuous_const
    intro U hU
    have hpre : F ⁻¹' U ∈ nhds (0 : ℝ) :=
      hFc.continuousAt.preimage_mem_nhds (by rw [hF0]; exact hU)
    have hsmall : {ε : ℝ | l₁ * |sin ε| < l₂} ∈ nhds (0 : ℝ) :=
      IsOpen.mem_nhds (isOpen_lt (continuous_const.mul (continuous_abs.comp continuous_sin))
        continuous_const) (by simp [hl₂])
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hpre hsmall)
    set ε := min (r / 2) 1 with hεdef
    have hε0 : 0 < ε := lt_min (half_pos hr) one_pos
    have hεr : ε < r := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
    have hε1 : ε ≤ 1 := min_le_right _ _
    obtain ⟨hεU, hεs⟩ := hball (show ε ∈ Metric.ball (0 : ℝ) r by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε0]
      exact hεr)
    have hεs' : l₁ * |sin ε| < l₂ := hεs
    have hsinε : 0 < sin ε := sin_pos_of_pos_of_lt_pi hε0 (by linarith [two_le_pi])
    have harg : |-(l₁ / l₂) * cos (θ 0) * cos a * sin ε| ≤ 1 := by
      rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_div, abs_of_pos hl₁, abs_of_pos hl₂,
        div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_one hl₂]
      have h1 : |cos (θ 0)| * |cos a| ≤ 1 := by
        simpa using mul_le_mul (abs_cos_le_one (θ 0)) (abs_cos_le_one a) (abs_nonneg _) zero_le_one
      have h2 : 0 ≤ l₁ * |sin ε| := by positivity
      calc l₁ * |cos (θ 0)| * |cos a| * |sin ε| = (|cos (θ 0)| * |cos a|) * (l₁ * |sin ε|) := by
            ring
        _ ≤ 1 * (l₁ * |sin ε|) := mul_le_mul_of_nonneg_right h1 h2
        _ ≤ l₂ := by linarith
    have hsinδ : sin (δ ε) = -(l₁ / l₂) * cos (θ 0) * cos a * sin ε :=
      sin_arcsin (abs_le.1 harg).1 (abs_le.1 harg).2
    have hmem : F ε ∈ (sliderCrank l₁ l₂ l₃).admissible := by
      refine (sliderCrank_mem_admissible_iff l₁ l₂ l₃ (θε ε) (dε ε)).2 ⟨⟨k, ?_⟩, ?_, ?_⟩
      · simp only [θε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        linarith
      · simp only [θε, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [show θ 0 + ε + (θ 1 + δ ε - ε) = a + δ ε by rw [ha]; ring, sin_add, sin_add, h0, hsa,
          hsinδ]
        field_simp
        linear_combination (-(l₁ * cos (θ 0) * sin ε)) * hca
      · simp only [θε, dε, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [show θ 0 + ε + (θ 1 + δ ε - ε) = a + δ ε by rw [ha]; ring]
    have hsin1 : sin (θε ε 0) ≠ 0 := by
      simp only [θε, Matrix.cons_val_zero]
      rw [sin_add, h0, zero_mul, zero_add]
      have hc : cos (θ 0) ≠ 0 := fun hc => by rw [hc] at hc0; norm_num at hc0
      exact mul_ne_zero hc hsinε.ne'
    refine ⟨F ε, hεU, hmem, ?_⟩
    rw [hrank, sliderCrank_structureRank l₃ hl₁ hl₂ hne hmem]
    simp only [hsin1, ↓reduceIte]
    exact one_pos

/-! ### Actuator singularities -/

private theorem scr_pair_vec (a b c x y z a' b' c' x' y' z' : ℝ) :
    Wrench.pair ⟨vec a b c, vec x y z⟩ ⟨vec a' b' c', vec x' y' z'⟩ =
      a * a' + b * b' + c * c' + x * x' + y * y' + z * z' := by
  simp [Wrench.pair, vec, PiLp.inner_apply, Fin.sum_univ_three]
  ring

private theorem scr_pair (F : Wrench) (a b c x y z : ℝ) :
    Wrench.pair F ⟨vec a b c, vec x y z⟩ =
      F.force 0 * a + F.force 1 * b + F.force 2 * c + F.torque 0 * x + F.torque 1 * y +
        F.torque 2 * z := by
  simp [Wrench.pair, vec, PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- **MLS Exercise 20(d), p. 152: with `d` active there is no actuator singularity** (p. 141):
the actuated slide transmits every wrench, at every configuration and for all lengths. -/
theorem sliderCrank_not_isActuatorSingular_slide (l₁ l₂ l₃ : ℝ)
    (Θ : (i : Fin 2) → Fin (![3, 1] i) → ℝ) :
    ¬ (sliderCrank l₁ l₂ l₃).IsActuatorSingular sliderCrankSlideActuated Θ := by
  intro hs
  apply hs
  rw [eq_top_iff]
  intro F _
  apply Submodule.mem_iSup_of_mem 1
  intro l hl
  exact absurd (show l ∈ sliderCrankSlideActuated 1 from (rfl : ((1 : Fin 2) : ℕ) = 1)) hl

/-- **MLS Exercise 20(e), p. 152: the actuator singularities with `θ₁` active** (p. 141). For
`l₂ ≠ 0`, at every configuration the mechanism is actuator singular exactly when
`cos(θ₁ + θ₂) = 0`, the rod perpendicular to the slide line. -/
theorem sliderCrank_isActuatorSingular_crank_iff {l₂ : ℝ} (l₁ l₃ : ℝ) (hl₂ : l₂ ≠ 0)
    (θ : Fin 3 → ℝ) (d : ℝ) :
    (sliderCrank l₁ l₂ l₃).IsActuatorSingular sliderCrankCrankActuated (sliderCrankConfig θ d) ↔
      cos (θ 0 + θ 1) = 0 := by
  have hJ := sliderCrankLinkage_spatialJacobian l₁ l₂ l₃ θ
  have hK := sliderCrankSlide_spatialJacobian ![d]
  constructor
  · intro hsing
    by_contra hc
    apply hsing
    rw [eq_top_iff]
    intro F _
    set W : Wrench := ⟨vec (cos (θ 0 + θ 1)) (sin (θ 0 + θ 1)) 0,
      vec 0 0 (l₁ * cos (θ 0) * sin (θ 0 + θ 1) - l₁ * sin (θ 0) * cos (θ 0 + θ 1))⟩ with hWdef
    have hW : W ∈ (sliderCrank l₁ l₂ l₃).transmissibleWrenches sliderCrankCrankActuated
        (sliderCrankConfig θ d) 0 := by
      intro l hl
      change Wrench.pair W ((sliderCrankLinkage l₁ l₂ l₃).spatialJacobian θ l) = 0
      rw [hJ]
      fin_cases l
      · exact absurd ⟨rfl, rfl⟩ hl
      · simp [hWdef, scr_pair_vec]
        ring
      · simp [hWdef, scr_pair_vec]
        ring
    have hR : F - (F.force 0 / cos (θ 0 + θ 1)) • W ∈
        (sliderCrank l₁ l₂ l₃).transmissibleWrenches sliderCrankCrankActuated
          (sliderCrankConfig θ d) 1 := by
      intro l _
      change Wrench.pair _ (sliderCrankSlide.spatialJacobian ![d] l) = 0
      rw [hK, Subsingleton.elim (α := Fin 1) l 0]
      have hWf : W.force 0 = cos (θ 0 + θ 1) := by simp [hWdef, vec]
      simp only [Matrix.cons_val_zero, scr_pair, Wrench.sub_force,
        Wrench.smul_force, Wrench.sub_torque, Wrench.smul_torque, PiLp.sub_apply,
        PiLp.smul_apply, smul_eq_mul, mul_zero, add_zero, mul_one, hWf]
      field_simp
      ring
    have hsum := add_mem (Submodule.mem_iSup_of_mem 0
      (Submodule.smul_mem _ (F.force 0 / cos (θ 0 + θ 1)) hW))
      (Submodule.mem_iSup_of_mem (ι := Fin 2)
        (p := fun i => (sliderCrank l₁ l₂ l₃).transmissibleWrenches sliderCrankCrankActuated
          (sliderCrankConfig θ d) i) 1 hR)
    rw [add_sub_cancel] at hsum
    exact hsum
  · intro hc
    have hs2 : sin (θ 0 + θ 1) ^ 2 = 1 := by nlinarith [sin_sq_add_cos_sq (θ 0 + θ 1)]
    have hsne : sin (θ 0 + θ 1) ≠ 0 := fun h0 => by rw [h0] at hs2; norm_num at hs2
    let φ : Wrench →ₗ[ℝ] ℝ :=
      { toFun := fun F => F.force 0
        map_add' := fun F G => by simp
        map_smul' := fun c F => by simp }
    have hle : (sliderCrank l₁ l₂ l₃).actuatorWrenches sliderCrankCrankActuated
        (sliderCrankConfig θ d) ≤ LinearMap.ker φ := by
      apply iSup_le
      intro i
      fin_cases i
      · intro F hF
        have h1 := hF ⟨1, by decide⟩ (fun h => absurd h.2 (by decide))
        have h2 := hF ⟨2, by decide⟩ (fun h => absurd h.2 (by decide))
        change Wrench.pair F ((sliderCrankLinkage l₁ l₂ l₃).spatialJacobian θ 1) = 0 at h1
        change Wrench.pair F ((sliderCrankLinkage l₁ l₂ l₃).spatialJacobian θ 2) = 0 at h2
        rw [hJ] at h1 h2
        simp [scr_pair] at h1 h2
        change F.force 0 = 0
        have : l₂ * sin (θ 0 + θ 1) * F.force 0 = 0 := by
          linear_combination h2 - h1 + (l₂ * F.force 1) * hc
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (mul_ne_zero hl₂ hsne)
        · exact h
      · intro F hF
        have h1 := hF ⟨0, by decide⟩ (fun h => absurd h.1 (by decide))
        change Wrench.pair F (sliderCrankSlide.spatialJacobian ![d] 0) = 0 at h1
        rw [hK] at h1
        simp only [Matrix.cons_val_zero, scr_pair] at h1
        change F.force 0 = 0
        linarith
    intro htop
    have hmem : (⟨vec 1 0 0, vec 0 0 0⟩ : Wrench) ∈ LinearMap.ker φ :=
      hle (htop ▸ Submodule.mem_top)
    change (vec 1 0 0) 0 = 0 at hmem
    simp [vec] at hmem

/-- **MLS Exercise 20(e), p. 152: when singular configurations exist with `θ₁` active.** For
positive `l₁, l₂` and every `l₃`, some configuration of `Q′` is actuator singular exactly when
`l₂ ≤ l₁` (the rod is not longer than the crank). -/
theorem sliderCrank_exists_isActuatorSingular_crank_iff {l₁ l₂ : ℝ} (l₃ : ℝ) (hl₁ : 0 < l₁)
    (hl₂ : 0 < l₂) :
    (∃ θ d, sliderCrankConfig θ d ∈ (sliderCrank l₁ l₂ l₃).admissible ∧
        (sliderCrank l₁ l₂ l₃).IsActuatorSingular sliderCrankCrankActuated
          (sliderCrankConfig θ d)) ↔ l₂ ≤ l₁ := by
  constructor
  · rintro ⟨θ, d, hQ, hsing⟩
    have hc := (sliderCrank_isActuatorSingular_crank_iff l₁ l₃ hl₂.ne' θ d).1 hsing
    have hs := ((sliderCrank_mem_admissible_iff l₁ l₂ l₃ θ d).1 hQ).2.1
    have hs2 : sin (θ 0 + θ 1) ^ 2 = 1 := by nlinarith [sin_sq_add_cos_sq (θ 0 + θ 1)]
    have hsq : l₂ ^ 2 ≤ l₁ ^ 2 := by
      have h1 : l₂ ^ 2 = (l₁ * sin (θ 0)) ^ 2 := by
        rw [show l₁ * sin (θ 0) = -(l₂ * sin (θ 0 + θ 1)) by linarith]
        linear_combination (-l₂ ^ 2) * hs2
      rw [h1, mul_pow]
      nlinarith [sin_sq_le_one (θ 0), sq_nonneg l₁]
    nlinarith
  · intro hle
    have hr : l₂ / l₁ ≤ 1 := (div_le_one hl₁).2 hle
    have hr' : -1 ≤ l₂ / l₁ := by
      have : 0 ≤ l₂ / l₁ := div_nonneg hl₂.le hl₁.le
      linarith
    refine ⟨![arcsin (l₂ / l₁), -(π / 2) - arcsin (l₂ / l₁), π / 2],
      l₁ * cos (arcsin (l₂ / l₁)) + l₃, ?_, ?_⟩
    · refine (sliderCrank_mem_admissible_iff l₁ l₂ l₃ _ _).2 ⟨⟨0, ?_⟩, ?_, ?_⟩
      · simp
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [show arcsin (l₂ / l₁) + (-(π / 2) - arcsin (l₂ / l₁)) = -(π / 2) by ring, sin_neg,
          sin_pi_div_two, sin_arcsin hr' hr]
        field_simp
        ring
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [show arcsin (l₂ / l₁) + (-(π / 2) - arcsin (l₂ / l₁)) = -(π / 2) by ring, cos_neg,
          cos_pi_div_two]
        ring
    · rw [sliderCrank_isActuatorSingular_crank_iff l₁ l₃ hl₂.ne']
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [show arcsin (l₂ / l₁) + (-(π / 2) - arcsin (l₂ / l₁)) = -(π / 2) by ring, cos_neg,
        cos_pi_div_two]

end Examples

end RoboLean
