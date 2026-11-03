import RoboLean.Kinematics.Jacobian
import RoboLean.Examples.RigidTransform
import RoboLean.Geometry.ElementaryRotations
import RoboLean.Kinematics.SphericalWristAngles

/-!
# Three manipulators of MLS Figure 3.23: Exercise 3(a) and the spatial Jacobians of 3(c)

MLS Chapter 3, Exercise 3, printed p. 146, Figure 3.23 (p. 146). The figure draws four three
degree of freedom manipulators without dimensions, in an oblique projection with `x` to the right,
`z` up and the depth direction `y` drawn at `45°`. This module reads three of them, with the base
frame at the marked point where the axes of `θ₁` and `θ₂` meet, `z` along the axis of `θ₁`, `y`
along the drawn axis of `θ₂`, `x` along the arm in the drawn configuration (the reference
configuration `θ = 0`), and the length symbols below (not printed in the figure):

* (i) `figureManipulatorRollPitchYaw l₁`: revolute joints about `+z`, `+y` and `+x` through the
  origin (the axis of `θ₃` is the arm's own axis), the tool on the arm at `(l₁, 0, 0)`;
* (iii) `figureManipulatorElbow l₁ l₂`: revolute joints about `+z` and `+y` through the origin and
  about `+y` through the elbow `(l₁, 0, 0)`, the tool at `(l₁ + l₂, 0, 0)`;
* (iv) `figureManipulatorPolar l₁`: revolute joints about `+z` and `+y` through the origin and a
  prismatic joint along the arm `+x`, the tool at `(l₁, 0, 0)` when `θ₃ = 0`.

The reference tool frames are parallel to the base frame. For each manipulator the forward
kinematics is the product of exponentials (eq. (3.3), p. 87) written as a rotation and a position,
and the spatial and body Jacobians (eqs. (3.54)–(3.55), pp. 116–117) are given column by column.
Exercise 3(b) is stated for (i) at the level of poses (a pose is reached exactly when its position
is `l₁` along its rotated first axis) and for (iii) and (iv) at the level of tool positions (the
distance from the shoulder fixes the third joint, as in Subproblem 3). Positive rotations follow
the right-hand rule about the drawn axis directions. Conventions: twists `(v, ω)`, Lean joint `k` is
the book's joint `k + 1`, `sᵢ = sin θᵢ`, `cᵢ = cos θᵢ`.
-/

noncomputable section

open Real

namespace RoboLean

namespace Examples

open RoboLean.Rotation (xAxis yAxis zAxis)

/-! ### Private coordinate helpers -/

private theorem fm_norm_zAxis : ‖zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [zAxis, Fin.sum_univ_succ]

private theorem fm_act_Z (t x y z : ℝ) :
    (Rotation.exp (vec 0 0 1) t).act (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z := by
  ext i
  rw [Rotation.act_apply, show vec 0 0 1 = zAxis from rfl, Rotation.exp_zAxis_val]
  fin_cases i <;>
    simp [Rotation.zMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec, sub_eq_add_neg]

private theorem fm_act_Y (t x y z : ℝ) :
    (Rotation.exp (vec 0 1 0) t).act (vec x y z) =
      vec (cos t * x + sin t * z) y (-(sin t * x) + cos t * z) := by
  ext i
  rw [Rotation.act_apply, show vec 0 1 0 = yAxis from rfl, Rotation.exp_yAxis_val]
  fin_cases i <;> simp [Rotation.yMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec]

private theorem fm_act_X (t x y z : ℝ) :
    (Rotation.exp (vec 1 0 0) t).act (vec x y z) =
      vec x (cos t * y - sin t * z) (sin t * y + cos t * z) := by
  ext i
  rw [Rotation.act_apply, show vec 1 0 0 = xAxis from rfl, Rotation.exp_xAxis_val]
  fin_cases i <;>
    simp [Rotation.xMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec, sub_eq_add_neg]

private theorem fm_vec_sub (a b c d e f : ℝ) :
    vec a b c - vec d e f = vec (a - d) (b - e) (c - f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem fm_vec_add (a b c d e f : ℝ) :
    vec a b c + vec d e f = vec (a + d) (b + e) (c + f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem fm_vec_smul (r a b c : ℝ) : r • vec a b c = vec (r * a) (r * b) (r * c) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem fm_vec_eq {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    vec a b c = vec a' b' c' := by
  rw [ha, hb, hc]

private theorem fm_xAxis : xAxis = vec 1 0 0 := rfl
private theorem fm_yAxis : yAxis = vec 0 1 0 := rfl
private theorem fm_zAxis : zAxis = vec 0 0 1 := rfl

private theorem fm_revolute_vec (a b c x y z : ℝ) :
    Twist.revolute (vec a b c) (vec x y z) =
      ⟨vec (-(b * z - c * y)) (-(c * x - a * z)) (-(a * y - b * x)), vec a b c⟩ := by
  apply Twist.ext <;> ext i <;> fin_cases i <;>
    simp [Twist.revolute, Vec3.cross, cross_apply, vec]

private theorem fm_applyPoint_rev {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) (x : Vec3) :
    (Twist.exp (Twist.revolute ω q) t).applyPoint x = (Rotation.exp ω t).act (x - q) + q :=
  Twist.exp_revolute_applyPoint ω q hω t x

private theorem fm_applyVector_rev (ω q : Vec3) (t : ℝ) (v : Vec3) :
    (Twist.exp (Twist.revolute ω q) t).applyVector v = (Rotation.exp ω t).act v := by
  simp [RigidTransform.applyVector, Twist.revolute]

private theorem fm_applyPoint_pri (u : Vec3) (t : ℝ) (x : Vec3) :
    (Twist.exp (Twist.prismatic u) t).applyPoint x = x + t • u := by
  rw [Twist.exp_prismatic]
  simp [RigidTransform.applyPoint]

private theorem fm_applyVector_pri (u : Vec3) (t : ℝ) (v : Vec3) :
    (Twist.exp (Twist.prismatic u) t).applyVector v = v := by
  rw [Twist.exp_prismatic]
  simp [RigidTransform.applyVector]

private theorem fm_translation (g : RigidTransform) :
    g.translation = g.applyPoint (vec 0 0 0) := by
  have : vec 0 0 0 = 0 := by
    ext i
    fin_cases i <;> rfl
  simp [RigidTransform.applyPoint, this]

private theorem fm_cross_vec (a b c d e f : ℝ) :
    Vec3.cross (vec a b c) (vec d e f) = vec (b * f - c * e) (c * d - a * f) (a * e - b * d) := by
  ext i
  fin_cases i <;> simp [Vec3.cross, cross_apply, vec]

private theorem fm_neg_vec (a b c : ℝ) : -vec a b c = vec (-a) (-b) (-c) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem fm_inv_twist_exp (ξ : Twist) (t : ℝ) : (Twist.exp ξ t)⁻¹ = Twist.exp ξ (-t) :=
  (Twist.exp_neg ξ t).symm

private theorem fm_tool_inv (a b c : ℝ) :
    (⟨1, vec a b c⟩ : RigidTransform)⁻¹ = ⟨1, vec (-a) (-b) (-c)⟩ := by
  apply RigidTransform.ext
  · simp
  · ext i
    fin_cases i <;> simp [vec]

private theorem fm_norm_sq_vec (a b c : ℝ) : ‖vec a b c‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [vec, Fin.sum_univ_succ]
  ring

private theorem fm_rpy_act (a b c l : ℝ) :
    (Rotation.exp zAxis a * Rotation.exp yAxis b * Rotation.exp xAxis c).act (vec l 0 0) =
      vec (l * (cos a * cos b)) (l * (sin a * cos b)) (-(l * sin b)) := by
  rw [Rotation.act_mul, Rotation.act_mul, fm_xAxis, fm_act_X, fm_yAxis, fm_act_Y, fm_zAxis,
    fm_act_Z]
  apply fm_vec_eq <;> ring

private theorem fm_tool_applyPoint (a b c : ℝ) :
    (⟨1, vec a b c⟩ : RigidTransform).applyPoint (vec 0 0 0) = vec a b c := by
  ext i
  fin_cases i <;> simp [RigidTransform.applyPoint, vec]

/-- **MLS Figure 3.23(iv), p. 146: the polar (RRP) manipulator**, revolute joints about `+z` and
`+y` through the base origin and a prismatic joint along `+x`; reference tool pose
`(I, (l₁, 0, 0))`. Twists `(-ω × q, ω)` and `(v, 0)`, order `(v, ω)`. -/
def figureManipulatorPolar (l₁ : ℝ) : SerialChain 3 where
  twist := ![Twist.revolute zAxis (vec 0 0 0), Twist.revolute yAxis (vec 0 0 0),
    Twist.prismatic xAxis]
  toolRef := ⟨1, vec l₁ 0 0⟩

/-- **MLS Exercise 3(a), p. 146, for Figure 3.23(iv): the forward kinematics of the polar
manipulator** (eq. (3.3), p. 87): `g(θ) = (Rz(θ₁) Ry(θ₂), (l₁ + θ₃)(c₁c₂, s₁c₂, -s₂))`. -/
theorem figureManipulatorPolar_fk (l₁ : ℝ) (θ : Fin 3 → ℝ) :
    (figureManipulatorPolar l₁).fk θ =
      ⟨Rotation.exp zAxis (θ 0) * Rotation.exp yAxis (θ 1),
        vec ((l₁ + θ 2) * (cos (θ 0) * cos (θ 1))) ((l₁ + θ 2) * (sin (θ 0) * cos (θ 1)))
          (-((l₁ + θ 2) * sin (θ 1)))⟩ := by
  apply RigidTransform.ext
  · simp [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
      figureManipulatorPolar, Twist.revolute, Twist.prismatic, mul_assoc]
  · rw [fm_translation]
    simp only [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
      List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, RigidTransform.mul_applyPoint]
    simp [figureManipulatorPolar, fm_tool_applyPoint, fm_applyPoint_rev fm_norm_zAxis,
      fm_applyPoint_rev Rotation.norm_yAxis, fm_applyPoint_pri]
    simp [fm_xAxis, fm_yAxis, fm_zAxis, fm_vec_sub, fm_vec_add, fm_vec_smul, fm_act_Z, fm_act_Y]
    apply fm_vec_eq <;> ring


/-- **MLS Exercise 3(c), p. 146, for Figure 3.23(iv): the spatial Jacobian of the polar
manipulator** (eq. (3.54), p. 116), order `(v, ω)`: `ξ₁ = (0, 0, 0, 0, 0, 1)`,
`ξ₂′ = (0, 0, 0, -s₁, c₁, 0)` and `ξ₃′ = (c₁c₂, s₁c₂, -s₂, 0, 0, 0)`. -/
theorem figureManipulatorPolar_spatialJacobian (l₁ : ℝ) (θ : Fin 3 → ℝ) :
    (figureManipulatorPolar l₁).spatialJacobian θ =
      ![⟨vec 0 0 0, vec 0 0 1⟩, ⟨vec 0 0 0, vec (-sin (θ 0)) (cos (θ 0)) 0⟩,
        ⟨vec (cos (θ 0) * cos (θ 1)) (sin (θ 0) * cos (θ 1)) (-sin (θ 1)), vec 0 0 0⟩] := by
  funext i
  fin_cases i <;>
    simp [SerialChain.spatialJacobian, SerialChain.jointMotions, figureManipulatorPolar,
      List.ofFn_succ, Twist.adjoint_revolute, Twist.adjoint_prismatic,
      fm_applyPoint_rev fm_norm_zAxis, fm_applyVector_rev] <;>
    simp [fm_xAxis, fm_yAxis, fm_zAxis, fm_act_Z, fm_act_Y, fm_revolute_vec]
  all_goals apply Twist.ext
  all_goals first
    | (apply fm_vec_eq <;> ring)
    | (simp only [Twist.prismatic]
       ext j
       fin_cases j <;> simp [vec])



/-- **MLS Exercise 3(c), p. 146, for Figure 3.23(iv): the body Jacobian of the polar manipulator**
(eq. (3.55), p. 117), order `(v, ω)`: `ξ₁† = (0, (l₁ + θ₃)c₂, 0, -s₂, 0, c₂)`,
`ξ₂† = (0, 0, -(l₁ + θ₃), 0, 1, 0)` and `ξ₃† = (1, 0, 0, 0, 0, 0)`. -/
theorem figureManipulatorPolar_bodyJacobian (l₁ : ℝ) (θ : Fin 3 → ℝ) :
    (figureManipulatorPolar l₁).bodyJacobian θ =
      ![⟨vec 0 ((l₁ + θ 2) * cos (θ 1)) 0, vec (-sin (θ 1)) 0 (cos (θ 1))⟩,
        ⟨vec 0 0 (-(l₁ + θ 2)), vec 0 1 0⟩, ⟨vec 1 0 0, vec 0 0 0⟩] := by
  funext i
  fin_cases i <;>
    simp [-Twist.exp_neg, -Rotation.exp_neg, SerialChain.bodyJacobian, SerialChain.jointMotions,
      figureManipulatorPolar, List.ofFn_succ, mul_inv_rev, fm_inv_twist_exp, fm_tool_inv,
      Twist.adjoint_revolute, Twist.adjoint_prismatic, fm_applyPoint_rev fm_norm_zAxis,
      fm_applyPoint_rev Rotation.norm_yAxis,
      fm_applyVector_rev, fm_applyPoint_pri, fm_applyVector_pri] <;>
    simp [-Rotation.exp_neg, Twist.prismatic, RigidTransform.applyPoint,
      RigidTransform.applyVector, fm_xAxis, fm_yAxis, fm_zAxis, fm_vec_add,
      fm_vec_smul, fm_neg_vec, fm_act_Z, fm_act_Y, fm_revolute_vec]
  all_goals first
    | (ext j
       fin_cases j <;> simp [vec]
       done)
    | (apply fm_vec_eq <;> ring_nf)


/-- **MLS Exercise 3(b), p. 146, for Figure 3.23(iv): inverse kinematics of the polar manipulator
for a tool position** (the distance from the shoulder fixes the prismatic coordinate, as in
Subproblem 3, p. 101): some angles `θ₁, θ₂` put the tool at `p` with prismatic coordinate `θ₃`
exactly when `(l₁ + θ₃)² = ‖p‖²`. -/
theorem figureManipulatorPolar_exists_translation_eq_iff (l₁ θ₃ : ℝ) (p : Vec3) :
    (∃ θ₁ θ₂ : ℝ, ((figureManipulatorPolar l₁).fk ![θ₁, θ₂, θ₃]).translation = p) ↔
      (l₁ + θ₃) ^ 2 = ‖p‖ ^ 2 := by
  have hp : p = vec (p 0) (p 1) (p 2) := by
    ext i
    fin_cases i <;> rfl
  constructor
  · rintro ⟨θ₁, θ₂, h⟩
    rw [figureManipulatorPolar_fk] at h
    rw [← h, fm_norm_sq_vec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    linear_combination (-((l₁ + θ₃) ^ 2 * cos θ₂ ^ 2)) * sin_sq_add_cos_sq θ₁ -
      (l₁ + θ₃) ^ 2 * sin_sq_add_cos_sq θ₂
  · intro h
    have hn : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = (l₁ + θ₃) ^ 2 := by
      rw [← fm_norm_sq_vec, ← hp, h]
    by_cases hr : l₁ + θ₃ = 0
    · rw [hr] at hn
      have h0 : p 0 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), sq_nonneg (p 2)]
      have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), sq_nonneg (p 2)]
      have h2 : p 2 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), sq_nonneg (p 2)]
      refine ⟨0, 0, ?_⟩
      rw [figureManipulatorPolar_fk, hp, h0, h1, h2]
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hr, zero_mul, neg_zero]
    · set r := l₁ + θ₃ with hrdef
      have hu : (p 0 / r) ^ 2 + (p 1 / r) ^ 2 + (p 2 / r) ^ 2 = 1 := by
        field_simp
        linarith
      have hu2 : (-(p 2 / r)) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (p 0 / r), sq_nonneg (p 1 / r)]
      have hb := abs_le.1 ((sq_le_one_iff_abs_le_one _).1 hu2)
      set z : ℂ := ⟨p 0 / r, p 1 / r⟩ with hz
      have hzn : ‖z‖ = √((p 0 / r) ^ 2 + (p 1 / r) ^ 2) := Complex.norm_eq_sqrt_sq_add_sq z
      have hc2 : cos (arcsin (-(p 2 / r))) = ‖z‖ := by
        rw [Real.cos_arcsin, hzn]
        congr 1
        linarith
      have key : ∀ w : ℝ, (‖z‖ = 0 → w = 0) → w / ‖z‖ * ‖z‖ = w := fun w hw => by
        by_cases h0 : ‖z‖ = 0
        · rw [hw h0, zero_div, zero_mul]
        · exact div_mul_cancel₀ w h0
      have hz0 : ‖z‖ = 0 → p 0 / r = 0 ∧ p 1 / r = 0 := fun h0 => by
        have := norm_eq_zero.1 h0
        rw [hz, Complex.ext_iff] at this
        exact this
      refine ⟨Complex.arg z, arcsin (-(p 2 / r)), ?_⟩
      rw [figureManipulatorPolar_fk]
      conv_rhs => rw [hp]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, ← hrdef]
      apply fm_vec_eq
      · rw [hc2]
        by_cases h0 : z = 0
        · obtain ⟨e0, -⟩ := hz0 (by rw [h0, norm_zero])
          rw [h0, norm_zero, mul_zero, mul_zero]
          field_simp at e0
          rw [e0, mul_zero]
        · rw [Complex.cos_arg h0, key _ (fun h' => (hz0 h').1)]
          field_simp
      · rw [hc2, Complex.sin_arg, key _ (fun h' => (hz0 h').2)]
        field_simp
      · rw [sin_arcsin hb.1 hb.2]
        field_simp

/-- **MLS Figure 3.23(iii), p. 146: the elbow (RRR) manipulator**, revolute joints about `+z` and
`+y` through the base origin and about `+y` through the elbow `(l₁, 0, 0)`; reference tool pose
`(I, (l₁ + l₂, 0, 0))`. Twists `(-ω × q, ω)`, order `(v, ω)`. -/
def figureManipulatorElbow (l₁ l₂ : ℝ) : SerialChain 3 where
  twist := ![Twist.revolute zAxis (vec 0 0 0), Twist.revolute yAxis (vec 0 0 0),
    Twist.revolute yAxis (vec l₁ 0 0)]
  toolRef := ⟨1, vec (l₁ + l₂) 0 0⟩

/-- **MLS Exercise 3(a), p. 146, for Figure 3.23(iii): the forward kinematics of the elbow
manipulator** (eq. (3.3), p. 87): `g(θ) = (Rz(θ₁) Ry(θ₂ + θ₃), (c₁ r, s₁ r, -(l₁s₂ + l₂s₂₃)))`
with `r = l₁c₂ + l₂c₂₃`. -/
theorem figureManipulatorElbow_fk (l₁ l₂ : ℝ) (θ : Fin 3 → ℝ) :
    (figureManipulatorElbow l₁ l₂).fk θ =
      ⟨Rotation.exp zAxis (θ 0) * Rotation.exp yAxis (θ 1 + θ 2),
        vec (cos (θ 0) * (l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2)))
          (sin (θ 0) * (l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2)))
          (-(l₁ * sin (θ 1) + l₂ * sin (θ 1 + θ 2)))⟩ := by
  apply RigidTransform.ext
  · simp [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
      figureManipulatorElbow, Twist.revolute, mul_assoc, Rotation.exp_add]
  · rw [fm_translation]
    simp only [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
      List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, RigidTransform.mul_applyPoint]
    simp [figureManipulatorElbow, fm_tool_applyPoint, fm_applyPoint_rev fm_norm_zAxis,
      fm_applyPoint_rev Rotation.norm_yAxis]
    simp [fm_yAxis, fm_zAxis, fm_vec_sub, fm_vec_add, fm_act_Z, fm_act_Y]
    apply fm_vec_eq <;> simp only [sin_add, cos_add] <;> ring


/-- **MLS Exercise 3(c), p. 146, for Figure 3.23(iii): the spatial Jacobian of the elbow
manipulator** (eq. (3.54), p. 116), order `(v, ω)`: `ξ₁ = (0, 0, 0, 0, 0, 1)`,
`ξ₂′ = (0, 0, 0, -s₁, c₁, 0)` and `ξ₃′ = (l₁c₁s₂, l₁s₁s₂, l₁c₂, -s₁, c₁, 0)`, the revolute twist
about `(-s₁, c₁, 0)` through the moved elbow `(l₁c₁c₂, l₁s₁c₂, -l₁s₂)`. -/
theorem figureManipulatorElbow_spatialJacobian (l₁ l₂ : ℝ) (θ : Fin 3 → ℝ) :
    (figureManipulatorElbow l₁ l₂).spatialJacobian θ =
      ![⟨vec 0 0 0, vec 0 0 1⟩, ⟨vec 0 0 0, vec (-sin (θ 0)) (cos (θ 0)) 0⟩,
        ⟨vec (l₁ * (cos (θ 0) * sin (θ 1))) (l₁ * (sin (θ 0) * sin (θ 1))) (l₁ * cos (θ 1)),
          vec (-sin (θ 0)) (cos (θ 0)) 0⟩] := by
  funext i
  fin_cases i <;>
    simp [SerialChain.spatialJacobian, SerialChain.jointMotions, figureManipulatorElbow,
      List.ofFn_succ, Twist.adjoint_revolute, fm_applyPoint_rev fm_norm_zAxis,
      fm_applyPoint_rev Rotation.norm_yAxis, fm_applyVector_rev] <;>
    simp [fm_yAxis, fm_zAxis, fm_vec_sub, fm_vec_add, fm_act_Z, fm_act_Y, fm_revolute_vec]
  apply fm_vec_eq
  · ring
  · ring
  · linear_combination (cos (θ 1) * l₁) * sin_sq_add_cos_sq (θ 0)



/-- **MLS Exercise 3(c), p. 146, for Figure 3.23(iii): the body Jacobian of the elbow manipulator**
(eq. (3.55), p. 117), order `(v, ω)`: `ξ₁† = (0, l₁c₂ + l₂c₂₃, 0, -s₂₃, 0, c₂₃)`,
`ξ₂† = (l₁s₃, 0, -(l₁c₃ + l₂), 0, 1, 0)` and `ξ₃† = (0, 0, -l₂, 0, 1, 0)`. -/
theorem figureManipulatorElbow_bodyJacobian (l₁ l₂ : ℝ) (θ : Fin 3 → ℝ) :
    (figureManipulatorElbow l₁ l₂).bodyJacobian θ =
      ![⟨vec 0 (l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2)) 0,
          vec (-sin (θ 1 + θ 2)) 0 (cos (θ 1 + θ 2))⟩,
        ⟨vec (l₁ * sin (θ 2)) 0 (-(l₁ * cos (θ 2) + l₂)), vec 0 1 0⟩,
        ⟨vec 0 0 (-l₂), vec 0 1 0⟩] := by
  funext i
  fin_cases i <;>
    simp [-Twist.exp_neg, -Rotation.exp_neg, SerialChain.bodyJacobian, SerialChain.jointMotions,
      figureManipulatorElbow, List.ofFn_succ, mul_inv_rev, fm_inv_twist_exp, fm_tool_inv,
      Twist.adjoint_revolute, fm_applyPoint_rev fm_norm_zAxis,
      fm_applyPoint_rev Rotation.norm_yAxis,
      fm_applyVector_rev] <;>
    simp [-Rotation.exp_neg, RigidTransform.applyPoint,
      RigidTransform.applyVector, fm_yAxis, fm_zAxis, fm_vec_sub, fm_vec_add,
      fm_act_Z, fm_act_Y, fm_revolute_vec]
  all_goals (try refine ⟨?_, ?_⟩)
  all_goals first
    | (ext j
       fin_cases j <;> simp [vec]
       done)
    | (apply fm_vec_eq <;> (try simp only [sin_add, cos_add]) <;> (try ring_nf) <;>
        (try simp only [cos_sq']) <;> ring1)


/-- **MLS Exercise 3(b), p. 146, for Figure 3.23(iii): inverse kinematics of the elbow manipulator
for a tool position** (Subproblem 3, p. 101: the distance from the shoulder fixes the elbow angle):
some angles `θ₁, θ₂` put the tool at `p` with elbow angle `θ₃` exactly when
`‖p‖² = l₁² + l₂² + 2 l₁ l₂ cos θ₃`. -/
theorem figureManipulatorElbow_exists_translation_eq_iff (l₁ l₂ θ₃ : ℝ) (p : Vec3) :
    (∃ θ₁ θ₂ : ℝ, ((figureManipulatorElbow l₁ l₂).fk ![θ₁, θ₂, θ₃]).translation = p) ↔
      ‖p‖ ^ 2 = l₁ ^ 2 + l₂ ^ 2 + 2 * l₁ * l₂ * cos θ₃ := by
  constructor
  · rintro ⟨θ₁, θ₂, h⟩
    rw [figureManipulatorElbow_fk] at h
    rw [← h, fm_norm_sq_vec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, cos_add, sin_add]
    linear_combination
      (l₁ * cos θ₂ + l₂ * (cos θ₂ * cos θ₃ - sin θ₂ * sin θ₃)) ^ 2 * sin_sq_add_cos_sq θ₁ +
        (l₁ ^ 2 + l₂ ^ 2 * (sin θ₃ ^ 2 + cos θ₃ ^ 2) + 2 * l₁ * l₂ * cos θ₃) *
          sin_sq_add_cos_sq θ₂ + l₂ ^ 2 * sin_sq_add_cos_sq θ₃
  · intro h
    obtain ⟨α, β, hαβ⟩ := (figureManipulatorPolar_exists_translation_eq_iff ‖p‖ 0 p).2 (by ring)
    rw [figureManipulatorPolar_fk] at hαβ
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, add_zero] at hαβ
    set z : ℂ := ⟨l₁ + l₂ * cos θ₃, l₂ * sin θ₃⟩ with hzdef
    set ψ := Complex.arg z with hψ
    have hz : ‖z‖ = ‖p‖ := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, hzdef, ← Real.sqrt_sq (norm_nonneg p), h]
      congr 1
      linear_combination l₂ ^ 2 * sin_sq_add_cos_sq θ₃
    have hA : ‖z‖ * cos ψ = l₁ + l₂ * cos θ₃ := Complex.norm_mul_cos_arg z
    have hB : ‖z‖ * sin ψ = l₂ * sin θ₃ := Complex.norm_mul_sin_arg z
    have key1 : l₁ * cos (β - ψ) + l₂ * cos (β - ψ + θ₃) = ‖p‖ * cos β := by
      rw [← hz, cos_add, cos_sub, sin_sub]
      linear_combination (-(cos β * cos ψ + sin β * sin ψ)) * hA +
        (sin β * cos ψ - cos β * sin ψ) * hB + ‖z‖ * cos β * sin_sq_add_cos_sq ψ
    have key2 : l₁ * sin (β - ψ) + l₂ * sin (β - ψ + θ₃) = ‖p‖ * sin β := by
      rw [← hz, sin_add, cos_sub, sin_sub]
      linear_combination (-(sin β * cos ψ - cos β * sin ψ)) * hA -
        (cos β * cos ψ + sin β * sin ψ) * hB + ‖z‖ * sin β * sin_sq_add_cos_sq ψ
    refine ⟨α, β - ψ, ?_⟩
    rw [figureManipulatorElbow_fk, ← hαβ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [key1, key2]
    apply fm_vec_eq <;> ring

/-- **MLS Figure 3.23(i), p. 146: the roll–pitch–yaw (RRR) manipulator**, revolute joints about
`+z`, `+y` and `+x` all through the base origin (the axis of `θ₃` is the arm); reference tool pose
`(I, (l₁, 0, 0))`. Twists `(-ω × q, ω)`, order `(v, ω)`. -/
def figureManipulatorRollPitchYaw (l₁ : ℝ) : SerialChain 3 where
  twist := ![Twist.revolute zAxis (vec 0 0 0), Twist.revolute yAxis (vec 0 0 0),
    Twist.revolute xAxis (vec 0 0 0)]
  toolRef := ⟨1, vec l₁ 0 0⟩

/-- **MLS Exercise 3(a), p. 146, for Figure 3.23(i): the forward kinematics of the roll–pitch–yaw
manipulator** (eq. (3.3), p. 87): `g(θ) = (Rz(θ₁) Ry(θ₂) Rx(θ₃), l₁(c₁c₂, s₁c₂, -s₂))`; the roll
`θ₃` does not move the tool point. -/
theorem figureManipulatorRollPitchYaw_fk (l₁ : ℝ) (θ : Fin 3 → ℝ) :
    (figureManipulatorRollPitchYaw l₁).fk θ =
      ⟨Rotation.exp zAxis (θ 0) * Rotation.exp yAxis (θ 1) * Rotation.exp xAxis (θ 2),
        vec (l₁ * (cos (θ 0) * cos (θ 1))) (l₁ * (sin (θ 0) * cos (θ 1))) (-(l₁ * sin (θ 1)))⟩ := by
  apply RigidTransform.ext
  · simp [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
      figureManipulatorRollPitchYaw, Twist.revolute, mul_assoc]
  · rw [fm_translation]
    simp only [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
      List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, RigidTransform.mul_applyPoint]
    simp [figureManipulatorRollPitchYaw, fm_tool_applyPoint, fm_applyPoint_rev fm_norm_zAxis,
      fm_applyPoint_rev Rotation.norm_yAxis, fm_applyPoint_rev Rotation.norm_xAxis]
    simp [fm_xAxis, fm_yAxis, fm_zAxis, fm_vec_sub, fm_vec_add, fm_act_Z, fm_act_Y, fm_act_X]
    apply fm_vec_eq <;> ring


/-- **MLS Exercise 3(c), p. 146, for Figure 3.23(i): the spatial Jacobian of the roll–pitch–yaw
manipulator** (eq. (3.54), p. 116), order `(v, ω)`: `ξ₁ = (0, 0, 0, 0, 0, 1)`,
`ξ₂′ = (0, 0, 0, -s₁, c₁, 0)` and `ξ₃′ = (0, 0, 0, c₁c₂, s₁c₂, -s₂)`, pure rotations about axes
through the origin. -/
theorem figureManipulatorRollPitchYaw_spatialJacobian (l₁ : ℝ) (θ : Fin 3 → ℝ) :
    (figureManipulatorRollPitchYaw l₁).spatialJacobian θ =
      ![⟨vec 0 0 0, vec 0 0 1⟩, ⟨vec 0 0 0, vec (-sin (θ 0)) (cos (θ 0)) 0⟩,
        ⟨vec 0 0 0, vec (cos (θ 0) * cos (θ 1)) (sin (θ 0) * cos (θ 1)) (-sin (θ 1))⟩] := by
  funext i
  fin_cases i <;>
    simp [SerialChain.spatialJacobian, SerialChain.jointMotions, figureManipulatorRollPitchYaw,
      List.ofFn_succ, Twist.adjoint_revolute, fm_applyPoint_rev fm_norm_zAxis,
      fm_applyPoint_rev Rotation.norm_yAxis, fm_applyVector_rev] <;>
    simp [fm_xAxis, fm_yAxis, fm_zAxis, fm_act_Z, fm_act_Y, fm_revolute_vec]



/-- **MLS Exercise 3(c), p. 146, for Figure 3.23(i): the body Jacobian of the roll–pitch–yaw
manipulator** (eq. (3.55), p. 117), order `(v, ω)`: `ξ₁† = (0, l₁c₂c₃, -l₁c₂s₃, -s₂, c₂s₃, c₂c₃)`,
`ξ₂† = (0, -l₁s₃, -l₁c₃, 0, c₃, -s₃)` and `ξ₃† = (0, 0, 0, 1, 0, 0)`. -/
theorem figureManipulatorRollPitchYaw_bodyJacobian (l₁ : ℝ) (θ : Fin 3 → ℝ) :
    (figureManipulatorRollPitchYaw l₁).bodyJacobian θ =
      ![⟨vec 0 (l₁ * (cos (θ 1) * cos (θ 2))) (-(l₁ * (cos (θ 1) * sin (θ 2)))),
          vec (-sin (θ 1)) (cos (θ 1) * sin (θ 2)) (cos (θ 1) * cos (θ 2))⟩,
        ⟨vec 0 (-(l₁ * sin (θ 2))) (-(l₁ * cos (θ 2))), vec 0 (cos (θ 2)) (-sin (θ 2))⟩,
        ⟨vec 0 0 0, vec 1 0 0⟩] := by
  funext i
  fin_cases i <;>
    simp [-Twist.exp_neg, -Rotation.exp_neg, SerialChain.bodyJacobian, SerialChain.jointMotions,
      figureManipulatorRollPitchYaw, List.ofFn_succ, mul_inv_rev, fm_inv_twist_exp, fm_tool_inv,
      Twist.adjoint_revolute, fm_applyPoint_rev fm_norm_zAxis,
      fm_applyPoint_rev Rotation.norm_yAxis, fm_applyPoint_rev Rotation.norm_xAxis,
      fm_applyVector_rev] <;>
    simp [-Rotation.exp_neg, RigidTransform.applyPoint,
      RigidTransform.applyVector, fm_xAxis, fm_yAxis, fm_zAxis, fm_vec_add,
      fm_act_Z, fm_act_Y, fm_act_X, fm_revolute_vec]
  all_goals (try refine ⟨?_, ?_⟩)
  all_goals first
    | (ext j
       fin_cases j <;> simp [vec]
       done)
    | (apply fm_vec_eq <;> ring_nf)


/-- **MLS Exercise 3(b), p. 146, for Figure 3.23(i): inverse kinematics of the roll–pitch–yaw
manipulator.** A pose `g` is reached exactly when its position is `l₁` along its rotated first
axis, `p = R (l₁, 0, 0)`; every rotation is reached (three-axis angles about `z, y, x`, p. 96). -/
theorem figureManipulatorRollPitchYaw_exists_fk_eq_iff (l₁ : ℝ) (g : RigidTransform) :
    (∃ θ : Fin 3 → ℝ, (figureManipulatorRollPitchYaw l₁).fk θ = g) ↔
      g.translation = g.rotation.act (vec l₁ 0 0) := by
  constructor
  · rintro ⟨θ, rfl⟩
    rw [figureManipulatorRollPitchYaw_fk]
    exact (fm_rpy_act _ _ _ _).symm
  · intro h
    have hzy : inner ℝ zAxis yAxis = 0 := by
      simp [zAxis, yAxis, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
    have hyx : inner ℝ yAxis xAxis = 0 := by
      simp [xAxis, yAxis, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
    obtain ⟨α, β, γ, hR⟩ := Rotation.exists_exp_mul_exp_mul_exp_eq fm_norm_zAxis
      Rotation.norm_yAxis Rotation.norm_xAxis hzy hyx g.rotation
    refine ⟨![α, β, γ], ?_⟩
    rw [figureManipulatorRollPitchYaw_fk]
    apply RigidTransform.ext
    · exact hR
    · rw [h, ← hR, fm_rpy_act]
      rfl

end Examples

end RoboLean
