import RoboLean.Kinematics.ParallelMechanism
import RoboLean.Examples.RigidTransform
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The variable geometry truss of MLS Exercise 21, parts (b)–(e)

MLS Chapter 3, Exercise 21, printed pp. 152–153 (figure on p. 152), with the definitions of
§5.2, pp. 132–135, and the actuator singularity of p. 141. The figure shows two base pivots a
distance `h` apart on a vertical line, the base frame `B` midway between them, and a platform with
two pivots at the same spacing `h`, the tool frame `T` midway between them. Leg `d₁` joins the upper
base pivot to the upper platform pivot, leg `d₂` the lower base pivot to the lower platform pivot,
and leg `d₃` the lower base pivot to the upper platform pivot; each leg is a revolute joint at the
base, an actuated prismatic joint and a revolute joint at the platform.

Zero configuration (the exercise asks for one to be fixed): every leg has length `0` and points
along `+x`, both revolute angles are `0`, and the platform is upright. Leg `i` is the chain
`trussLeg aᵢ bᵢ` with base pivot `(0, aᵢ)` and platform pivot at `(0, bᵢ)` in the tool frame:
`(a, b) = (h/2, h/2)`, `(-h/2, -h/2)` and `(-h/2, h/2)`. Its joint coordinates are `α` (leg
direction from `+x`, counterclockwise), the signed leg length `d` (no actuator limits, as the
exercise assumes) and `β` (platform angle relative to the leg). With these coordinates the zero
configuration lies in `Q′` only for `h = 0`; the coordinates are the leg lengths themselves.

Contents:

* (b) the forward kinematics of a leg and the structure equations: a configuration lies in `Q′`
  exactly when the three legs reach one platform pose `((x, y), R_φ)`;
* (c) the leg lengths: a leg reaches `((x, y), R_φ)` with length `d` exactly when
  `d² = ‖(x, y) + R_φ (0, b) - (0, a)‖²`, written out for the three legs;
* (d) the instantaneous twists of every leg, order `(v, ω)`; legs `d₂, d₃` share their first twist
  (the common base pivot) and on `Q′` legs `d₁, d₃` share their last twist (the common platform
  pivot);
* (e) with the prismatic joints actuated and every leg of nonzero length, the truss is actuator
  singular exactly when `cos α₁ · sin(α₃ - α₂) = 0`: leg `d₁` parallel to the base line or legs
  `d₂, d₃` parallel (geometrically, on `Q′` the first puts legs `d₁` and `d₃` on one line and the
  second puts legs `d₂` and `d₃` on one line through the common base pivot; not stated here);
* (e) with every leg of nonzero length the admissible tool velocities are all the planar twists, so
  such a configuration is not kinematically singular.

These are statements about the coordinate model, not about a physical truss.
-/

noncomputable section

open Real

namespace RoboLean

namespace Examples

/-! ### Private coordinate helpers -/

private theorem tr_norm_zAxis : ‖Rotation.zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [Rotation.zAxis, Fin.sum_univ_succ]

private theorem tr_zRotation_act (t x y z : ℝ) :
    (Rotation.zRotation t).act (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z := by
  ext i
  fin_cases i <;>
    simp [Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, vec]
  all_goals ring

private theorem tr_vec_eq {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    vec a b c = vec a' b' c' := by
  rw [ha, hb, hc]

private theorem tr_exp_z_applyPoint (qx qy qz t x y z : ℝ) :
    (Twist.exp (Twist.revolute Rotation.zAxis (vec qx qy qz)) t).applyPoint (vec x y z) =
      vec (cos t * (x - qx) - sin t * (y - qy) + qx)
        (sin t * (x - qx) + cos t * (y - qy) + qy) z := by
  rw [Twist.exp_revolute_applyPoint _ _ tr_norm_zAxis]
  have : vec x y z - vec qx qy qz = vec (x - qx) (y - qy) (z - qz) := by
    ext i
    fin_cases i <;> simp [vec]
  rw [this, show Rotation.exp Rotation.zAxis t = Rotation.zRotation t from rfl, tr_zRotation_act]
  ext i
  fin_cases i <;> simp [vec]

private theorem tr_exp_z_applyVector (q : Vec3) (t x y z : ℝ) :
    (Twist.exp (Twist.revolute Rotation.zAxis q) t).applyVector (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z := by
  simp only [RigidTransform.applyVector, Twist.exp_rotation, Twist.revolute]
  exact tr_zRotation_act t x y z

private theorem tr_exp_z_applyVector_z (q : Vec3) (t : ℝ) :
    (Twist.exp (Twist.revolute Rotation.zAxis q) t).applyVector Rotation.zAxis =
      Rotation.zAxis := by
  simp only [RigidTransform.applyVector, Twist.exp_rotation, Twist.revolute]
  exact Rotation.exp_act_unit_axis _ tr_norm_zAxis t

private theorem tr_exp_x_applyPoint (t x y z : ℝ) :
    (Twist.exp (Twist.prismatic (vec 1 0 0)) t).applyPoint (vec x y z) = vec (x + t) y z := by
  rw [Twist.exp_prismatic]
  ext i
  fin_cases i <;> simp [RigidTransform.applyPoint, vec]

private theorem tr_exp_x_applyVector (t : ℝ) (v : Vec3) :
    (Twist.exp (Twist.prismatic (vec 1 0 0)) t).applyVector v = v := by
  rw [Twist.exp_prismatic]
  simp [RigidTransform.applyVector]

private theorem tr_translation (g : RigidTransform) :
    g.translation = g.applyPoint (vec 0 0 0) := by
  have : vec 0 0 0 = 0 := by
    ext i
    fin_cases i <;> rfl
  simp [RigidTransform.applyPoint, this]

private theorem tr_vec_eq_iff (a b c a' b' c' : ℝ) :
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

private theorem tr_revolute_z (x y z : ℝ) :
    Twist.revolute Rotation.zAxis (vec x y z) = ⟨vec y (-x) 0, vec 0 0 1⟩ := by
  apply Twist.ext <;> ext i <;> fin_cases i <;>
    simp [Twist.revolute, Vec3.cross, cross_apply, Rotation.zAxis, vec]

private theorem tr_pair_vec (a b c x y z a' b' c' x' y' z' : ℝ) :
    Wrench.pair ⟨vec a b c, vec x y z⟩ ⟨vec a' b' c', vec x' y' z'⟩ =
      a * a' + b * b' + c * c' + x * x' + y * y' + z * z' := by
  simp [Wrench.pair, vec, PiLp.inner_apply, Fin.sum_univ_three]
  ring

private theorem tr_pair (F : Wrench) (a b c x y z : ℝ) :
    Wrench.pair F ⟨vec a b c, vec x y z⟩ =
      F.force 0 * a + F.force 1 * b + F.force 2 * c + F.torque 0 * x + F.torque 1 * y +
        F.torque 2 * z := by
  simp [Wrench.pair, vec, PiLp.inner_apply, Fin.sum_univ_three]
  ring

private theorem tr_zRotation_eq_iff (a b : ℝ) :
    Rotation.zRotation a = Rotation.zRotation b ↔ ∃ k : ℤ, a = b + k * (2 * π) := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    rw [Rotation.zRotation_val, Rotation.zRotation_val] at hv
    have hc := congrFun (congrFun hv 0) 0
    have hs := congrFun (congrFun hv 1) 0
    simp at hc hs
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (Real.Angle.cos_sin_inj hc hs)
    exact ⟨k, by linarith⟩
  · rintro ⟨k, rfl⟩
    exact Rotation.exp_add_int_mul_two_pi _ tr_norm_zAxis b k


/-- One leg of the variable geometry truss of MLS Exercise 21 (figure, p. 152): a revolute joint
about `+z` at the base pivot `(0, a, 0)`, a prismatic joint along `+x` and a revolute joint about
`+z` through the same point at the zero configuration (twists `(-ω × q, ω)` and `(v, 0)`, order
`(v, ω)`); the reference tool pose `(I, (0, a - b, 0))` puts the platform pivot `(0, b)` of the tool
frame on the base pivot. -/
def trussLeg (a b : ℝ) : SerialChain 3 where
  twist := ![Twist.revolute Rotation.zAxis (vec 0 a 0), Twist.prismatic (vec 1 0 0),
    Twist.revolute Rotation.zAxis (vec 0 a 0)]
  toolRef := ⟨1, vec 0 (a - b) 0⟩

/-- **MLS Exercise 21, p. 152: the variable geometry truss as a parallel mechanism** (§5.2,
p. 132) with pivot spacing `h`: leg `d₁` is `trussLeg (h/2) (h/2)`, leg `d₂` is
`trussLeg (-h/2) (-h/2)` and leg `d₃` is `trussLeg (-h/2) (h/2)`, base frame midway between the
base pivots and tool frame midway between the platform pivots. -/
def variableGeometryTruss (h : ℝ) : ParallelMechanism 3 (fun _ => 3) where
  chain := ![trussLeg (h / 2) (h / 2), trussLeg (-(h / 2)) (-(h / 2)), trussLeg (-(h / 2)) (h / 2)]

/-- The actuated joints of the variable geometry truss, MLS Exercise 21, p. 152: the prismatic
joint (Lean joint `1`) of every leg; the revolute joints are passive. -/
def trussActuated : (i : Fin 3) → Set (Fin ((fun _ : Fin 3 => 3) i)) :=
  fun _ => {j | (j : ℕ) = 1}

/-- **MLS Exercise 21(b), p. 152: forward kinematics of a leg** by the product of exponentials
(eq. (3.3), p. 87): `g(α, d, β) = (Rz(α + β), (d cos α + b sin(α + β), a + d sin α - b cos(α + β),
0))`, angles counterclockwise. -/
theorem trussLeg_fk (a b : ℝ) (θ : Fin 3 → ℝ) :
    (trussLeg a b).fk θ =
      ⟨Rotation.zRotation (θ 0 + θ 2),
        vec (θ 1 * cos (θ 0) + b * sin (θ 0 + θ 2)) (a + θ 1 * sin (θ 0) - b * cos (θ 0 + θ 2))
          0⟩ := by
  have hfk : (trussLeg a b).fk θ =
      Twist.exp (Twist.revolute Rotation.zAxis (vec 0 a 0)) (θ 0) *
        (Twist.exp (Twist.prismatic (vec 1 0 0)) (θ 1) *
          (Twist.exp (Twist.revolute Rotation.zAxis (vec 0 a 0)) (θ 2) * 1)) *
        ⟨1, vec 0 (a - b) 0⟩ := by
    simp only [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
      List.ofFn_zero, List.prod_cons, List.prod_nil]
    rfl
  apply RigidTransform.ext
  · rw [hfk]
    simp only [RigidTransform.mul_rotation, Twist.exp_rotation, Twist.revolute, Twist.prismatic,
      Rotation.exp_zero_axis, mul_one, one_mul]
    simp only [Rotation.zRotation]
    rw [Rotation.exp_add]
  · rw [tr_translation, hfk]
    simp only [RigidTransform.mul_applyPoint, RigidTransform.one_applyPoint]
    rw [show (⟨1, vec 0 (a - b) 0⟩ : RigidTransform).applyPoint (vec 0 0 0) =
        vec 0 (a - b) 0 from by
      ext i
      fin_cases i <;> simp [RigidTransform.applyPoint, vec]]
    rw [tr_exp_z_applyPoint, tr_exp_x_applyPoint, tr_exp_z_applyPoint]
    apply tr_vec_eq
    · simp only [sin_add]
      ring
    · simp only [cos_add]
      ring
    · rfl

/-- **MLS Exercise 21(b), p. 152: one leg reaching a platform pose.** The leg reaches
`((x, y), R_φ)` exactly when `α + β ≡ φ (mod 2π)`, `d cos α + b sin φ = x` and
`a + d sin α - b cos φ = y`. -/
theorem trussLeg_fk_eq_iff (a b : ℝ) (θ : Fin 3 → ℝ) (x y φ : ℝ) :
    (trussLeg a b).fk θ = ⟨Rotation.zRotation φ, vec x y 0⟩ ↔
      (∃ k : ℤ, θ 0 + θ 2 = φ + k * (2 * π)) ∧ θ 1 * cos (θ 0) + b * sin φ = x ∧
        a + θ 1 * sin (θ 0) - b * cos φ = y := by
  rw [trussLeg_fk]
  constructor
  · intro hfk
    obtain ⟨hR, hp⟩ := RigidTransform.mk.inj hfk
    obtain ⟨k, hk⟩ := (tr_zRotation_eq_iff _ _).1 hR
    obtain ⟨h0, h1, -⟩ := (tr_vec_eq_iff _ _ _ _ _ _).1 hp
    rw [hk, sin_add_int_mul_two_pi] at h0
    rw [hk, cos_add_int_mul_two_pi] at h1
    exact ⟨⟨k, hk⟩, h0, h1⟩
  · rintro ⟨⟨k, hk⟩, hx, hy⟩
    rw [(tr_zRotation_eq_iff _ _).2 ⟨k, hk⟩, hk, sin_add_int_mul_two_pi, cos_add_int_mul_two_pi,
      hx, hy]

/-- **MLS Exercise 21(b), p. 152: the structure equations** (eq. (3.65), p. 132). A configuration
of the truss lies in `Q′` exactly when the three legs reach one planar platform pose
`((x, y), R_φ)`. -/
theorem variableGeometryTruss_mem_admissible_iff (h : ℝ) (Θ : Fin 3 → Fin 3 → ℝ) :
    Θ ∈ (variableGeometryTruss h).admissible ↔
      ∃ x y φ : ℝ, ∀ i, ((variableGeometryTruss h).chain i).fk (Θ i) =
        ⟨Rotation.zRotation φ, vec x y 0⟩ := by
  constructor
  · rintro ⟨-, hQ⟩
    refine ⟨Θ 0 1 * cos (Θ 0 0) + h / 2 * sin (Θ 0 0 + Θ 0 2),
      h / 2 + Θ 0 1 * sin (Θ 0 0) - h / 2 * cos (Θ 0 0 + Θ 0 2), Θ 0 0 + Θ 0 2, fun i => ?_⟩
    rw [hQ i 0]
    exact trussLeg_fk _ _ _
  · rintro ⟨x, y, φ, H⟩
    exact ⟨fun i => by fin_cases i <;> exact Set.mem_univ _, fun i j => (H i).trans (H j).symm⟩

/-- **MLS Exercise 21(c), p. 152: the length of one leg.** For every target `((x, y), R_φ)`, some
angles `α, β` make the leg of length `d` reach it exactly when
`d² = (x - b sin φ)² + (y - a + b cos φ)²`, the squared distance from the base pivot `(0, a)` to
the platform pivot `(x, y) + R_φ (0, b)`; the sign of `d` is free (no actuator limits). -/
theorem trussLeg_exists_fk_eq_iff (a b x y φ d : ℝ) :
    (∃ α β : ℝ, (trussLeg a b).fk ![α, d, β] = ⟨Rotation.zRotation φ, vec x y 0⟩) ↔
      d ^ 2 = (x - b * sin φ) ^ 2 + (y - a + b * cos φ) ^ 2 := by
  constructor
  · rintro ⟨α, β, hfk⟩
    obtain ⟨-, hx, hy⟩ := (trussLeg_fk_eq_iff a b _ x y φ).1 hfk
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
    subst hx hy
    linear_combination (-d ^ 2) * sin_sq_add_cos_sq α
  · intro hd2
    by_cases hd : d = 0
    · subst hd
      have hu : x - b * sin φ = 0 := by
        nlinarith [sq_nonneg (x - b * sin φ), sq_nonneg (y - a + b * cos φ)]
      have hv : y - a + b * cos φ = 0 := by
        nlinarith [sq_nonneg (x - b * sin φ), sq_nonneg (y - a + b * cos φ)]
      refine ⟨0, φ, (trussLeg_fk_eq_iff a b _ x y φ).2 ⟨⟨0, by simp⟩, ?_, ?_⟩⟩
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        linarith
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        linarith
    · set z : ℂ := ⟨(x - b * sin φ) / d, (y - a + b * cos φ) / d⟩ with hz
      have hnorm : ‖z‖ = 1 := by
        rw [Complex.norm_eq_sqrt_sq_add_sq, hz, div_pow, div_pow, ← add_div, ← hd2,
          div_self (pow_ne_zero 2 hd), Real.sqrt_one]
      have hz0 : z ≠ 0 := fun h0 => by rw [h0, norm_zero] at hnorm; exact zero_ne_one hnorm
      refine ⟨Complex.arg z, φ - Complex.arg z,
        (trussLeg_fk_eq_iff a b _ x y φ).2 ⟨⟨0, by simp⟩, ?_, ?_⟩⟩
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [Complex.cos_arg hz0, hnorm, div_one, hz]
        field_simp
        ring
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [Complex.sin_arg, hnorm, div_one, hz]
        field_simp
        ring

/-- **MLS Exercise 21(c), p. 152: the three leg lengths for a given platform pose.** Configurations
reaching `g_st = ((x, y), R_φ)` with leg lengths `d = (d₁, d₂, d₃)` exist exactly when
`d₁² = (x - (h/2) sin φ)² + (y - h/2 + (h/2) cos φ)²`,
`d₂² = (x + (h/2) sin φ)² + (y + h/2 - (h/2) cos φ)²` and
`d₃² = (x - (h/2) sin φ)² + (y + h/2 + (h/2) cos φ)²`. -/
theorem variableGeometryTruss_exists_legLengths_iff (h x y φ : ℝ) (d : Fin 3 → ℝ) :
    (∃ Θ : Fin 3 → Fin 3 → ℝ, (∀ i, ((variableGeometryTruss h).chain i).fk (Θ i) =
        ⟨Rotation.zRotation φ, vec x y 0⟩) ∧ ∀ i, Θ i 1 = d i) ↔
      d 0 ^ 2 = (x - h / 2 * sin φ) ^ 2 + (y - h / 2 + h / 2 * cos φ) ^ 2 ∧
        d 1 ^ 2 = (x + h / 2 * sin φ) ^ 2 + (y + h / 2 - h / 2 * cos φ) ^ 2 ∧
          d 2 ^ 2 = (x - h / 2 * sin φ) ^ 2 + (y + h / 2 + h / 2 * cos φ) ^ 2 := by
  have key : ∀ (a b : ℝ) (i : Fin 3) (r : ℝ),
      (d i ^ 2 = (x - b * sin φ) ^ 2 + (y - a + b * cos φ) ^ 2 ↔
      d i ^ 2 = r) → ((∃ α β : ℝ, (trussLeg a b).fk ![α, d i, β] =
        ⟨Rotation.zRotation φ, vec x y 0⟩) ↔ d i ^ 2 = r) := fun a b i r hr =>
    (trussLeg_exists_fk_eq_iff a b x y φ (d i)).trans hr
  have h0 := key (h / 2) (h / 2) 0 ((x - h / 2 * sin φ) ^ 2 + (y - h / 2 + h / 2 * cos φ) ^ 2)
    (by constructor <;> intro e <;> linear_combination e)
  have h1 := key (-(h / 2)) (-(h / 2)) 1 ((x + h / 2 * sin φ) ^ 2 + (y + h / 2 - h / 2 * cos φ) ^ 2)
    (by constructor <;> intro e <;> linear_combination e)
  have h2 := key (-(h / 2)) (h / 2) 2 ((x - h / 2 * sin φ) ^ 2 + (y + h / 2 + h / 2 * cos φ) ^ 2)
    (by constructor <;> intro e <;> linear_combination e)
  have hΘ : ∀ (θ : Fin 3 → ℝ), θ = ![θ 0, θ 1, θ 2] := fun θ => by
    funext j
    fin_cases j <;> rfl
  constructor
  · rintro ⟨Θ, H, hd⟩
    refine ⟨h0.1 ⟨Θ 0 0, Θ 0 2, ?_⟩, h1.1 ⟨Θ 1 0, Θ 1 2, ?_⟩, h2.1 ⟨Θ 2 0, Θ 2 2, ?_⟩⟩
    · rw [← hd 0, ← hΘ (Θ 0)]
      exact H 0
    · rw [← hd 1, ← hΘ (Θ 1)]
      exact H 1
    · rw [← hd 2, ← hΘ (Θ 2)]
      exact H 2
  · rintro ⟨e0, e1, e2⟩
    obtain ⟨α₀, β₀, f0⟩ := h0.2 e0
    obtain ⟨α₁, β₁, f1⟩ := h1.2 e1
    obtain ⟨α₂, β₂, f2⟩ := h2.2 e2
    refine ⟨![![α₀, d 0, β₀], ![α₁, d 1, β₁], ![α₂, d 2, β₂]], fun i => ?_, fun i => ?_⟩
    · fin_cases i
      exacts [f0, f1, f2]
    · fin_cases i <;> rfl

/-- **MLS Exercise 21(d), p. 153: the instantaneous twists of a leg** (eq. (3.54), p. 116), order
`(v, ω)`: the base revolute `(a, 0, 0, 0, 0, 1)`, the prismatic joint `(cos α, sin α, 0, 0, 0, 0)`
along the leg, and the platform revolute through the platform pivot `(d cos α, a + d sin α)`,
`(a + d sin α, -d cos α, 0, 0, 0, 1)`. -/
theorem trussLeg_spatialJacobian (a b : ℝ) (θ : Fin 3 → ℝ) :
    (trussLeg a b).spatialJacobian θ =
      ![⟨vec a 0 0, vec 0 0 1⟩, ⟨vec (cos (θ 0)) (sin (θ 0)) 0, vec 0 0 0⟩,
        ⟨vec (a + θ 1 * sin (θ 0)) (-(θ 1 * cos (θ 0))) 0, vec 0 0 1⟩] := by
  funext i
  fin_cases i
  · show (trussLeg a b).spatialJacobian θ 0 = ⟨vec a 0 0, vec 0 0 1⟩
    rw [SerialChain.spatialJacobian_zero]
    change Twist.revolute Rotation.zAxis (vec 0 a 0) = _
    rw [tr_revolute_z]
    simp
  · change Twist.adjoint (((trussLeg a b).jointMotions θ).take 1).prod
      (Twist.prismatic (vec 1 0 0)) = _
    have hg : ((trussLeg a b).jointMotions θ).take 1 =
        [Twist.exp (Twist.revolute Rotation.zAxis (vec 0 a 0)) (θ 0)] := by
      simp [SerialChain.jointMotions, List.ofFn_succ, trussLeg]
    rw [hg, List.prod_singleton, Twist.adjoint_prismatic, tr_exp_z_applyVector]
    apply Twist.ext
    · show vec _ _ _ = vec _ _ _
      apply tr_vec_eq <;> ring
    · ext j
      fin_cases j <;> simp [Twist.prismatic, vec]
  · change Twist.adjoint (((trussLeg a b).jointMotions θ).take 2).prod
      (Twist.revolute Rotation.zAxis (vec 0 a 0)) = _
    have hg : ((trussLeg a b).jointMotions θ).take 2 =
        [Twist.exp (Twist.revolute Rotation.zAxis (vec 0 a 0)) (θ 0),
          Twist.exp (Twist.prismatic (vec 1 0 0)) (θ 1)] := by
      simp [SerialChain.jointMotions, List.ofFn_succ, trussLeg]
    rw [hg, List.prod_cons, List.prod_singleton, Twist.adjoint_revolute,
      RigidTransform.mul_applyVector, tr_exp_x_applyVector, tr_exp_z_applyVector_z,
      RigidTransform.mul_applyPoint, tr_exp_x_applyPoint, tr_exp_z_applyPoint, tr_revolute_z]
    congr 1
    apply tr_vec_eq <;> ring

/-- **MLS Exercise 21(d), p. 153: the links that meet at a point share twists.** Legs `d₂` and `d₃`
have the same base revolute twist at every configuration, and on `Q′` legs `d₁` and `d₃` have the
same platform revolute twist. -/
theorem variableGeometryTruss_spatialJacobian_shared (h : ℝ) (Θ : Fin 3 → Fin 3 → ℝ) :
    ((variableGeometryTruss h).chain 1).spatialJacobian (Θ 1) 0 =
        ((variableGeometryTruss h).chain 2).spatialJacobian (Θ 2) 0 ∧
      (Θ ∈ (variableGeometryTruss h).admissible →
        ((variableGeometryTruss h).chain 0).spatialJacobian (Θ 0) 2 =
          ((variableGeometryTruss h).chain 2).spatialJacobian (Θ 2) 2) := by
  refine ⟨?_, fun hQ => ?_⟩
  · show (trussLeg (-(h / 2)) (-(h / 2))).spatialJacobian (Θ 1) 0 =
      (trussLeg (-(h / 2)) (h / 2)).spatialJacobian (Θ 2) 0
    rw [trussLeg_spatialJacobian, trussLeg_spatialJacobian]
    rfl
  · have h02 := hQ.2 0 2
    change (trussLeg (h / 2) (h / 2)).fk (Θ 0) = (trussLeg (-(h / 2)) (h / 2)).fk (Θ 2) at h02
    rw [trussLeg_fk, trussLeg_fk] at h02
    obtain ⟨hR, hp⟩ := RigidTransform.mk.inj h02
    obtain ⟨k, hk⟩ := (tr_zRotation_eq_iff _ _).1 hR
    obtain ⟨hx, hy, -⟩ := (tr_vec_eq_iff _ _ _ _ _ _).1 hp
    rw [hk, sin_add_int_mul_two_pi] at hx
    rw [hk, cos_add_int_mul_two_pi] at hy
    show (trussLeg (h / 2) (h / 2)).spatialJacobian (Θ 0) 2 =
      (trussLeg (-(h / 2)) (h / 2)).spatialJacobian (Θ 2) 2
    rw [trussLeg_spatialJacobian, trussLeg_spatialJacobian]
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    congr 1
    apply tr_vec_eq <;> linarith

/-- **MLS Exercise 21(e), p. 153: the actuator singularities** (p. 141). With the prismatic joints
actuated, `h ≠ 0` and every leg of nonzero length, the truss is actuator singular exactly when
`cos α₁ · sin(α₃ - α₂) = 0`, with `αᵢ` the direction of leg `dᵢ` from `+x`. -/
theorem variableGeometryTruss_isActuatorSingular_iff {h : ℝ} (hh : h ≠ 0)
    (Θ : Fin 3 → Fin 3 → ℝ) (hd : ∀ i, Θ i 1 ≠ 0) :
    (variableGeometryTruss h).IsActuatorSingular trussActuated Θ ↔
      cos (Θ 0 0) * sin (Θ 2 0 - Θ 1 0) = 0 := by
  set A : Fin 3 → ℝ := ![h / 2, -(h / 2), -(h / 2)] with hA
  have hJ : ∀ i, ((variableGeometryTruss h).chain i).spatialJacobian (Θ i) =
      ![⟨vec (A i) 0 0, vec 0 0 1⟩, ⟨vec (cos (Θ i 0)) (sin (Θ i 0)) 0, vec 0 0 0⟩,
        ⟨vec (A i + Θ i 1 * sin (Θ i 0)) (-(Θ i 1 * cos (Θ i 0))) 0, vec 0 0 1⟩] := by
    intro i
    fin_cases i <;> exact trussLeg_spatialJacobian _ _ _
  have hmem : ∀ i (F : Wrench),
      F ∈ (variableGeometryTruss h).transmissibleWrenches trussActuated Θ i ↔
        F.force 0 * A i + F.torque 2 = 0 ∧
          F.force 0 * (A i + Θ i 1 * sin (Θ i 0)) - F.force 1 * (Θ i 1 * cos (Θ i 0)) +
            F.torque 2 = 0 := by
    intro i F
    constructor
    · intro hF
      have h0 := hF 0 (by simp [trussActuated])
      have h2 := hF 2 (by simp [trussActuated])
      rw [hJ i] at h0 h2
      change Wrench.pair F ⟨vec (A i) 0 0, vec 0 0 1⟩ = 0 at h0
      change Wrench.pair F ⟨vec (A i + Θ i 1 * sin (Θ i 0)) (-(Θ i 1 * cos (Θ i 0))) 0,
        vec 0 0 1⟩ = 0 at h2
      rw [tr_pair] at h0 h2
      constructor <;> linarith
    · rintro ⟨h0, h2⟩ l hl
      rw [hJ i]
      fin_cases l
      · change Wrench.pair F ⟨vec (A i) 0 0, vec 0 0 1⟩ = 0
        rw [tr_pair]
        linarith
      · exact absurd rfl hl
      · change Wrench.pair F ⟨vec (A i + Θ i 1 * sin (Θ i 0)) (-(Θ i 1 * cos (Θ i 0))) 0,
          vec 0 0 1⟩ = 0
        rw [tr_pair]
        linarith
  set M : Matrix (Fin 3) (Fin 3) ℝ := !![cos (Θ 0 0), cos (Θ 1 0), cos (Θ 2 0);
    sin (Θ 0 0), sin (Θ 1 0), sin (Θ 2 0);
    -(A 0 * cos (Θ 0 0)), -(A 1 * cos (Θ 1 0)), -(A 2 * cos (Θ 2 0))] with hM
  have hdet : M.det = -(h * (cos (Θ 0 0) * sin (Θ 2 0 - Θ 1 0))) := by
    rw [Matrix.det_fin_three, sin_sub]
    simp [hM, hA]
    ring
  constructor
  · intro hsing
    by_contra hD
    have hdet0 : M.det ≠ 0 := by
      rw [hdet, neg_ne_zero]
      exact mul_ne_zero hh hD
    apply hsing
    rw [eq_top_iff]
    intro F _
    set t : Fin 3 → ℝ := ![F.force 0, F.force 1, F.torque 2] with ht
    set k : Fin 3 → ℝ := M⁻¹.mulVec t with hk
    have hMk : M.mulVec k = t := by
      rw [hk, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet0),
        Matrix.one_mulVec]
    have e0 := congrFun hMk 0
    have e1 := congrFun hMk 1
    have e2 := congrFun hMk 2
    simp only [hM, ht, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.vecHead] at e0 e1 e2
    let W : Fin 3 → Wrench := fun i =>
      ⟨vec (cos (Θ i 0)) (sin (Θ i 0)) 0, vec 0 0 (-(A i * cos (Θ i 0)))⟩
    have hW : ∀ i, W i ∈ (variableGeometryTruss h).transmissibleWrenches trussActuated Θ i := by
      intro i
      rw [hmem]
      simp only [W, vec, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      constructor <;> ring
    set R : Wrench := F - (k 0 • W 0 + k 1 • W 1 + k 2 • W 2) with hR
    have hR0 : R.force 0 = 0 := by
      simp [hR, W, vec]
      linarith
    have hR1 : R.force 1 = 0 := by
      simp [hR, W, vec]
      linarith
    have hR2 : R.torque 2 = 0 := by
      simp [hR, W, vec]
      linarith
    have hRmem : R ∈ (variableGeometryTruss h).transmissibleWrenches trussActuated Θ 0 := by
      rw [hmem, hR0, hR1, hR2]
      constructor <;> ring
    have hsum := add_mem (add_mem (add_mem
      (Submodule.mem_iSup_of_mem (ι := Fin 3)
        (p := fun i => (variableGeometryTruss h).transmissibleWrenches trussActuated Θ i) 0
        (Submodule.smul_mem _ (k 0) (hW 0)))
      (Submodule.mem_iSup_of_mem (ι := Fin 3)
        (p := fun i => (variableGeometryTruss h).transmissibleWrenches trussActuated Θ i) 1
        (Submodule.smul_mem _ (k 1) (hW 1))))
      (Submodule.mem_iSup_of_mem (ι := Fin 3)
        (p := fun i => (variableGeometryTruss h).transmissibleWrenches trussActuated Θ i) 2
        (Submodule.smul_mem _ (k 2) (hW 2))))
      (Submodule.mem_iSup_of_mem (ι := Fin 3)
        (p := fun i => (variableGeometryTruss h).transmissibleWrenches trussActuated Θ i) 0 hRmem)
    rw [hR, add_sub_cancel] at hsum
    exact hsum
  · intro hD
    have hdet0 : M.det = 0 := by rw [hdet, hD, mul_zero, neg_zero]
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet0
    have hvj : ∀ j : Fin 3,
        v 0 * cos (Θ j 0) + v 1 * sin (Θ j 0) - v 2 * (A j * cos (Θ j 0)) = 0 := by
      intro j
      have := congrFun hv j
      fin_cases j <;>
        simp [hM, hA, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at this ⊢ <;> linarith
    let φ : Wrench →ₗ[ℝ] ℝ :=
      { toFun := fun F => F.force 0 * v 0 + F.force 1 * v 1 + F.torque 2 * v 2
        map_add' := fun F G => by simp; ring
        map_smul' := fun c F => by simp; ring }
    have hle : (variableGeometryTruss h).actuatorWrenches trussActuated Θ ≤ LinearMap.ker φ := by
      apply iSup_le
      intro i F hF
      obtain ⟨h0, h2⟩ := (hmem i F).1 hF
      have hK : F.force 0 * sin (Θ i 0) - F.force 1 * cos (Θ i 0) = 0 := by
        have : Θ i 1 * (F.force 0 * sin (Θ i 0) - F.force 1 * cos (Θ i 0)) = 0 := by
          linear_combination h2 - h0
        exact (mul_eq_zero.1 this).resolve_left (hd i)
      change F.force 0 * v 0 + F.force 1 * v 1 + F.torque 2 * v 2 = 0
      linear_combination (F.force 0 * cos (Θ i 0) + F.force 1 * sin (Θ i 0)) * hvj i +
        (sin (Θ i 0) * v 0 - cos (Θ i 0) * v 1 - A i * sin (Θ i 0) * v 2) * hK -
          (F.force 0 * v 0 + F.force 1 * v 1 - A i * F.force 0 * v 2) * sin_sq_add_cos_sq (Θ i 0) +
            v 2 * h0
    intro htop
    have hmemV : (⟨vec (v 0) (v 1) 0, vec 0 0 (v 2)⟩ : Wrench) ∈ LinearMap.ker φ :=
      hle (htop ▸ Submodule.mem_top)
    change (vec (v 0) (v 1) 0) 0 * v 0 + (vec (v 0) (v 1) 0) 1 * v 1 +
      (vec 0 0 (v 2)) 2 * v 2 = 0 at hmemV
    simp only [vec, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hmemV
    apply hv0
    funext j
    fin_cases j <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

/-- The twists of motions in the `xy`-plane, MLS p. 136 (planar twists `(v_x, v_y, ω)` written in
space as `(v_x, v_y, 0, 0, 0, ω)`, order `(v, ω)`): zero `v_z`, `ω_x` and `ω_y`. -/
def planarTwistSubmodule : Submodule ℝ Twist where
  carrier := {V | V.linear 2 = 0 ∧ V.angular 0 = 0 ∧ V.angular 1 = 0}
  add_mem' := by
    rintro V W ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp [h1, h2, h3, k1, k2, k3]
  zero_mem' := by simp
  smul_mem' := by
    rintro c V ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp [h1, h2, h3]

/-- **MLS Exercise 21(e), p. 153: the admissible velocities lie in the plane** (eq. (3.70),
p. 134): at every configuration of the truss every admissible tool velocity is a planar twist. -/
theorem variableGeometryTruss_admissibleVelocities_le (h : ℝ) (Θ : Fin 3 → Fin 3 → ℝ) :
    (variableGeometryTruss h).admissibleVelocities Θ ≤ planarTwistSubmodule := by
  refine (iInf_le _ 0).trans ?_
  rw [Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  change (trussLeg (h / 2) (h / 2)).spatialJacobian (Θ 0) l ∈ planarTwistSubmodule
  rw [trussLeg_spatialJacobian]
  fin_cases l <;> refine ⟨?_, ?_, ?_⟩ <;> simp [vec]

/-- **MLS Exercise 21(e), p. 153: with every leg of nonzero length all planar tool velocities are
admissible** (eqs. (3.69)–(3.70), p. 134). -/
theorem variableGeometryTruss_admissibleVelocities_eq {h : ℝ} (Θ : Fin 3 → Fin 3 → ℝ)
    (hd : ∀ i, Θ i 1 ≠ 0) :
    (variableGeometryTruss h).admissibleVelocities Θ = planarTwistSubmodule := by
  refine le_antisymm (variableGeometryTruss_admissibleVelocities_le h Θ) (le_iInf fun i => ?_)
  rintro V ⟨h1, h2, h3⟩
  rw [Submodule.mem_span_range_iff_exists_fun]
  set A : Fin 3 → ℝ := ![h / 2, -(h / 2), -(h / 2)] with hA
  have hJ : ((variableGeometryTruss h).chain i).spatialJacobian (Θ i) =
      ![⟨vec (A i) 0 0, vec 0 0 1⟩, ⟨vec (cos (Θ i 0)) (sin (Θ i 0)) 0, vec 0 0 0⟩,
        ⟨vec (A i + Θ i 1 * sin (Θ i 0)) (-(Θ i 1 * cos (Θ i 0))) 0, vec 0 0 1⟩] := by
    fin_cases i <;> exact trussLeg_spatialJacobian _ _ _
  rw [hJ]
  have hμ : (sin (Θ i 0) * (V.linear 0 - A i * V.angular 2) - cos (Θ i 0) * V.linear 1) /
      Θ i 1 * Θ i 1 =
        sin (Θ i 0) * (V.linear 0 - A i * V.angular 2) - cos (Θ i 0) * V.linear 1 :=
    div_mul_cancel₀ _ (hd i)
  refine ⟨![V.angular 2 - (sin (Θ i 0) * (V.linear 0 - A i * V.angular 2) -
      cos (Θ i 0) * V.linear 1) / Θ i 1,
    cos (Θ i 0) * (V.linear 0 - A i * V.angular 2) + sin (Θ i 0) * V.linear 1,
    (sin (Θ i 0) * (V.linear 0 - A i * V.angular 2) - cos (Θ i 0) * V.linear 1) / Θ i 1], ?_⟩
  apply Twist.ext <;> ext j <;> fin_cases j <;> simp [Fin.sum_univ_three, vec, h1, h2, h3]
  · linear_combination sin (Θ i 0) * hμ +
      (V.linear 0 - A i * V.angular 2) * sin_sq_add_cos_sq (Θ i 0)
  · linear_combination (-cos (Θ i 0)) * hμ + V.linear 1 * sin_sq_add_cos_sq (Θ i 0)

/-- **MLS Exercise 21(e), p. 153: kinematic singularities need a leg of zero length** (p. 134, in
the convention of `ParallelMechanism.IsKinematicallySingular`): a configuration whose three legs
have nonzero length is not kinematically singular, since its rank `ρ` is the largest possible. -/
theorem variableGeometryTruss_not_isKinematicallySingular {h : ℝ} (Θ : Fin 3 → Fin 3 → ℝ)
    (hd : ∀ i, Θ i 1 ≠ 0) : ¬ (variableGeometryTruss h).IsKinematicallySingular Θ := by
  intro hs
  obtain ⟨Θ₁, -, -, hlt⟩ := hs Set.univ Filter.univ_mem
  have hle : (variableGeometryTruss h).structureRank Θ₁ ≤
      (variableGeometryTruss h).structureRank Θ := by
    rw [ParallelMechanism.structureRank, ParallelMechanism.structureRank,
      variableGeometryTruss_admissibleVelocities_eq Θ hd]
    exact Submodule.finrank_mono (variableGeometryTruss_admissibleVelocities_le h Θ₁)
  omega

end Examples

end RoboLean
