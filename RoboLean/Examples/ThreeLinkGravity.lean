import RoboLean.Dynamics.PotentialEnergy
import RoboLean.Examples.RigidTransform
import RoboLean.Geometry.ElementaryRotations

/-!
# Gravity term of the three-link manipulator (MLS Example 4.3)

MLS Chapter 4, Example 4.3, printed pp. 172–175, Figure 4.5. The joint twists and the link
frames at the mass centers are the ones printed on p. 172; the heights `h₁, h₂, h₃` of the
mass centers are printed on p. 174, and the gravity term `N = ∂V/∂θ` with
`V = m₁ g h₁ + m₂ g h₂ + m₃ g h₃` is display (4.25), p. 175.

Here the arm is an `InertialChain 3` and the heights are computed from the general link poses
`g_{sl_k}(θ) = e^{ξ̂₁θ₁} ⋯ e^{ξ̂_kθ_k} g_{sl_k}(0)` (`InertialChain.linkPose_eq`) with upward
direction `up = +z` (gravity along `-z`); the gravity term is the gradient of the resulting
potential (`InertialChain.gravityTerm_eq_gradient`), from an explicit Fréchet derivative. None
of these values is taken from the book; they are compared with the printed ones.

Lean joint `k` is the book's joint `k + 1`, so `θ 1 = θ₂` and `θ 2 = θ₃`. The link masses
`![m₁, m₂, m₃]` passed to the potential are the masses in the link inertias. This is one
instance (a convention check on one chain, not a general theorem), and nothing here concerns a
physical manipulator.
-/

noncomputable section
open Matrix Filter Topology

namespace RoboLean.Examples

/-- **The joints of MLS Example 4.3 (p. 172, Figure 4.5)**, base-frame twists at `θ = 0` in the
order `(v, ω)`: a revolute joint about `+z` through the base origin, and two revolute joints
about `-x` through `(0, 0, l₀)` and `(0, l₁, l₀)`, giving the printed
`ξ₁ = (0, 0, 0, 0, 0, 1)`, `ξ₂ = (0, -l₀, 0, -1, 0, 0)`, `ξ₃ = (0, -l₀, l₁, -1, 0, 0)`
(`elbowChain_twist_coordinates`). Lean joint `k` is the book's joint `k + 1`. The tool pose is
not used by the dynamics and is set to the identity. -/
def elbowChain (l₀ l₁ : ℝ) : SerialChain 3 where
  twist := ![Twist.revolute Rotation.zAxis (vec 0 0 0),
    Twist.revolute (-Rotation.xAxis) (vec 0 0 l₀), Twist.revolute (-Rotation.xAxis) (vec 0 l₁ l₀)]
  toolRef := 1

/-- **The three-link manipulator of MLS Example 4.3 (p. 172, Figure 4.5) with inertial data.**
Link frames at the mass centers, with the base orientation at `θ = 0`, at the printed
`g_{sl₁}(0) = (0, 0, r₀)`, `g_{sl₂}(0) = (0, r₁, l₀)` and `g_{sl₃}(0) = (0, l₁ + r₂, l₀)`, and
generalized inertias `[[mᵢ I, 0], [0, diag(Iᵢ)]]` (the printed `𝓜ᵢ`, p. 172), with
`Iᵢ = ![I_xi, I_yi, I_zi]`. -/
def threeLinkArm (m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ : ℝ) (I₁ I₂ I₃ : Fin 3 → ℝ) : InertialChain 3 where
  chain := elbowChain l₀ l₁
  linkRef := ![⟨1, vec 0 0 r₀⟩, ⟨1, vec 0 r₁ l₀⟩, ⟨1, vec 0 (l₁ + r₂) l₀⟩]
  linkInertia := ![RigidBody.generalizedInertia m₁ (Matrix.diagonal I₁),
    RigidBody.generalizedInertia m₂ (Matrix.diagonal I₂),
    RigidBody.generalizedInertia m₃ (Matrix.diagonal I₃)]

/-- **The joint twists of MLS Example 4.3 as printed on p. 172**, in six coordinates (linear
first): `ξ₁ = (0, 0, 0, 0, 0, 1)`, `ξ₂ = (0, -l₀, 0, -1, 0, 0)`, `ξ₃ = (0, -l₀, l₁, -1, 0, 0)`
(Lean twist `k` is the book's `ξ_{k+1}`). -/
theorem elbowChain_twist_coordinates (l₀ l₁ : ℝ) :
    ((elbowChain l₀ l₁).twist 0).coordinates = Sum.elim ![0, 0, 0] ![0, 0, 1] ∧
      ((elbowChain l₀ l₁).twist 1).coordinates = Sum.elim ![0, -l₀, 0] ![-1, 0, 0] ∧
      ((elbowChain l₀ l₁).twist 2).coordinates = Sum.elim ![0, -l₀, l₁] ![-1, 0, 0] := by
  refine ⟨?_, ?_, ?_⟩ <;> funext r <;> rcases r with i | i <;> fin_cases i <;>
    simp [elbowChain, Twist.coordinates, Twist.revolute, Vec3.cross, cross_apply,
      Rotation.zAxis, Rotation.xAxis, vec]

private theorem norm_zAxis_eq_one : ‖Rotation.zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [Rotation.zAxis, Fin.sum_univ_succ]

private theorem norm_neg_xAxis : ‖-Rotation.xAxis‖ = 1 := by
  rw [norm_neg, Rotation.norm_xAxis]

private theorem exp_zAxis_act_vec (t x y z : ℝ) :
    (Rotation.exp Rotation.zAxis t).act (vec x y z) =
      vec (Real.cos t * x - Real.sin t * y) (Real.sin t * x + Real.cos t * y) z := by
  change (Rotation.zRotation t).act (vec x y z) = _
  ext i
  fin_cases i <;>
    simp [Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, vec]
  all_goals ring

private theorem exp_neg_xAxis_act_vec (t x y z : ℝ) :
    (Rotation.exp (-Rotation.xAxis) t).act (vec x y z) =
      vec x (Real.cos t * y + Real.sin t * z) (-(Real.sin t * y) + Real.cos t * z) := by
  rw [show -Rotation.xAxis = (-1 : ℝ) • Rotation.xAxis by simp, Rotation.exp_smul,
    Rotation.exp_xAxis]
  ext i
  fin_cases i <;>
    simp [Rotation.act_apply, Rotation.xRotation_val, Rotation.xMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, vec]

private theorem vec_add_vec (a b c a' b' c' : ℝ) :
    vec a b c + vec a' b' c' = vec (a + a') (b + b') (c + c') := by
  ext i
  fin_cases i <;> simp [vec]

private theorem vec_sub_vec (a b c a' b' c' : ℝ) :
    vec a b c - vec a' b' c' = vec (a - a') (b - b') (c - c') := by
  ext i
  fin_cases i <;> simp [vec]

private theorem translation_eq_applyPoint (g : RigidTransform) :
    g.translation = g.applyPoint (vec 0 0 0) := by
  have : vec 0 0 0 = 0 := by
    ext i
    fin_cases i <;> rfl
  simp [RigidTransform.applyPoint, this]

private theorem translation_applyPoint_eq (p x : Vec3) :
    (⟨1, p⟩ : RigidTransform).applyPoint x = x + p := by
  simp [RigidTransform.applyPoint]

private theorem inner_zAxis_vec (a b c : ℝ) : inner ℝ Rotation.zAxis (vec a b c) = c := by
  simp [Rotation.zAxis, vec, PiLp.inner_apply, Fin.sum_univ_three]

/-- **The heights of the link mass centers of MLS Example 4.3, as printed on p. 174**, computed
from the link poses with `up = +z`: `h₁ = r₀`, `h₂ = l₀ - r₁ sin θ₂`,
`h₃ = l₀ - l₁ sin θ₂ - r₂ sin(θ₂ + θ₃)` (Lean link `k` is the book's link `k + 1`,
`θ 1 = θ₂`, `θ 2 = θ₃`). -/
theorem threeLinkArm_linkHeight (m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ : ℝ) (I₁ I₂ I₃ : Fin 3 → ℝ)
    (θ : Fin 3 → ℝ) :
    (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkHeight Rotation.zAxis 0 θ = r₀ ∧
      (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkHeight Rotation.zAxis 1 θ =
        l₀ - r₁ * Real.sin (θ 1) ∧
      (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkHeight Rotation.zAxis 2 θ =
        l₀ - l₁ * Real.sin (θ 1) - r₂ * Real.sin (θ 1 + θ 2) := by
  have h0 : ∀ t x, (Twist.exp (Twist.revolute Rotation.zAxis (vec 0 0 0)) t).applyPoint x =
      (Rotation.exp Rotation.zAxis t).act (x - vec 0 0 0) + vec 0 0 0 :=
    Twist.exp_revolute_applyPoint _ _ norm_zAxis_eq_one
  have h1 : ∀ (q : Vec3) t x, (Twist.exp (Twist.revolute (-Rotation.xAxis) q) t).applyPoint x =
      (Rotation.exp (-Rotation.xAxis) t).act (x - q) + q :=
    fun q => Twist.exp_revolute_applyPoint _ q norm_neg_xAxis
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [InertialChain.linkHeight, InertialChain.linkPose_eq, translation_eq_applyPoint]
    simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_zero,
      Fin.val_one, Fin.val_two, List.take_succ_cons, List.take_zero, List.prod_cons,
      List.prod_nil, mul_one, RigidTransform.mul_applyPoint]
    simp only [threeLinkArm, elbowChain, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, translation_applyPoint_eq, h0, h1, vec_add_vec, vec_sub_vec,
      exp_zAxis_act_vec, exp_neg_xAxis_act_vec, inner_zAxis_vec]
    try simp only [Real.sin_add]
    ring

/-- **The potential energy of MLS Example 4.3 (p. 174)**, `V = m₁ g h₁ + m₂ g h₂ + m₃ g h₃` with
the printed heights, for link masses `![m₁, m₂, m₃]`, gravitational constant `g` and `up = +z`.
-/
theorem threeLinkArm_potentialEnergy (m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ : ℝ) (I₁ I₂ I₃ : Fin 3 → ℝ)
    (g : ℝ) (θ : Fin 3 → ℝ) :
    (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).potentialEnergy ![m₁, m₂, m₃] g
        Rotation.zAxis θ =
      m₁ * g * r₀ + m₂ * g * (l₀ - r₁ * Real.sin (θ 1)) +
        m₃ * g * (l₀ - l₁ * Real.sin (θ 1) - r₂ * Real.sin (θ 1 + θ 2)) := by
  obtain ⟨h0, h1, h2⟩ := threeLinkArm_linkHeight m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃ θ
  rw [InertialChain.potentialEnergy, Fin.sum_univ_three, h0, h1, h2]
  simp

/-- **The gravity term of MLS Example 4.3, eq. (4.25), p. 175**, `N = ∂V/∂θ` for the potential
of `threeLinkArm_potentialEnergy` (`up = +z`): `N₁ = 0`,
`N₂ = -(m₂ g r₁ + m₃ g l₁) cos θ₂ - m₃ g r₂ cos(θ₂ + θ₃)`, `N₃ = -m₃ g r₂ cos(θ₂ + θ₃)`.

Observation (consistency check), not an errata judgment: the printed display (4.25), p. 175,
shows the second entry as `−(m₂gr₁ + m₃gl₁) cos θ₂ − m₃r₂ cos(θ₂+θ₃))`, without the factor `g`
in the last term and with an unbalanced parenthesis. This theorem states the derivative of the
heights printed on p. 174, which carries `g` in that term. -/
theorem threeLinkArm_gravityTerm (m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ : ℝ) (I₁ I₂ I₃ : Fin 3 → ℝ)
    (g : ℝ) (θ : Fin 3 → ℝ) :
    (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).gravityTerm ![m₁, m₂, m₃] g
        Rotation.zAxis θ =
      ![0, -(m₂ * g * r₁ + m₃ * g * l₁) * Real.cos (θ 1) - m₃ * g * r₂ * Real.cos (θ 1 + θ 2),
        -(m₃ * g * r₂ * Real.cos (θ 1 + θ 2))] := by
  have hV : (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).potentialEnergy ![m₁, m₂, m₃] g
      Rotation.zAxis = fun q => m₁ * g * r₀ + m₂ * g * (l₀ - r₁ * Real.sin (q 1)) +
        m₃ * g * (l₀ - l₁ * Real.sin (q 1) - r₂ * Real.sin (q 1 + q 2)) := by
    funext q
    exact threeLinkArm_potentialEnergy m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃ g q
  have hc1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 1 θ
  have hc2 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 2 θ
  have hd := ((((hc1.sin.const_mul r₁).const_sub l₀).const_mul (m₂ * g)).const_add
    (m₁ * g * r₀)).fun_add
    ((((hc1.sin.const_mul l₁).const_sub l₀).fun_sub ((hc1.fun_add hc2).sin.const_mul r₂)
      ).const_mul (m₃ * g))
  rw [← hV] at hd
  rw [InertialChain.gravityTerm_eq_gradient _ hd]
  funext i
  fin_cases i <;> simp [Lagrangian.gradient] <;> ring

end RoboLean.Examples
