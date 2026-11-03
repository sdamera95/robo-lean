import RoboLean.Kinematics.Jacobian
import RoboLean.Examples.RigidTransform
import RoboLean.Geometry.ElementaryRotations

/-!
# The Stanford arm and its spatial Jacobian: MLS Example 3.9

MLS printed pp. 119–120, Figure 3.14. The idealized Stanford arm has two revolute joints at the
base through `q₁ = q₂ = (0, 0, l₀)` with axes `ω₁ = (0, 0, 1)` and `ω₂ = (-1, 0, 0)` (so that
`ω₂' = e^{ẑθ₁}(-1, 0, 0) = (-cos θ₁, -sin θ₁, 0)`), a prismatic joint along `(0, 1, 0)` (so that
`v₃' = e^{ẑθ₁} e^{-x̂θ₂} (0, 1, 0)`), and a spherical wrist at `q_w = (0, l₁, l₀)` with axes
`(0, 0, 1)`, `(-1, 0, 0)` and `(0, 1, 0)` (the directions `ω₄' = e^{ẑθ₁} e^{-x̂θ₂} (0, 0, 1)`,
`ω₅' = e^{ẑθ₁} e^{-x̂θ₂} e^{ẑθ₄} (-1, 0, 0)`, `ω₆' = e^{ẑθ₁} e^{-x̂θ₂} e^{ẑθ₄} e^{-x̂θ₅} (0, 1, 0)`
printed on p. 120). The reference tool frame is placed at the wrist centre; the spatial Jacobian
does not depend on it.

The theorem `stanfordArm_spatialJacobian` checks every column of the printed Jacobian (3.58)
against the columns of `SerialChain.spatialJacobian` (MLS eq. (3.54), p. 116), computed from the
twists: `ξ₁`, `ξ₂' = (l₀ s₁, -l₀ c₁, 0, -c₁, -s₁, 0)`, `ξ₃' = (v₃', 0)` with
`v₃' = (-s₁ c₂, c₁ c₂, -s₂)`, and `(-ωᵢ' × q_w', ωᵢ')` for the wrist with the printed `ωᵢ'` and
`q_w' = (-(l₁ + θ₃) s₁ c₂, (l₁ + θ₃) c₁ c₂, l₀ - (l₁ + θ₃) s₂)`.

Conventions: twists `(v, ω)`, Lean joint `k` is the book's joint `k + 1`, `sᵢ = sin θᵢ`,
`cᵢ = cos θᵢ`, all lengths and joint values real.
-/

noncomputable section

open Real

namespace RoboLean

namespace Examples

open RoboLean.Rotation (xAxis yAxis zAxis)

private theorem st_norm_zAxis : ‖zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [zAxis, Fin.sum_univ_succ]

private theorem st_norm_neg_xAxis : ‖-xAxis‖ = 1 := by
  rw [norm_neg, Rotation.norm_xAxis]

private theorem st_act_negX (t x y z : ℝ) :
    (Rotation.exp (-xAxis) t).act (vec x y z) =
      vec x (cos t * y + sin t * z) (-(sin t * y) + cos t * z) := by
  rw [Rotation.exp_neg_axis]
  ext i
  rw [Rotation.act_apply, Rotation.exp_xAxis_val]
  fin_cases i <;> simp [Rotation.xMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec]

private theorem st_act_Z (t x y z : ℝ) :
    (Rotation.exp zAxis t).act (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z := by
  ext i
  rw [Rotation.act_apply, Rotation.exp_zAxis_val]
  fin_cases i <;>
    simp [Rotation.zMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec, sub_eq_add_neg]

private theorem st_act_Z' (t x y z : ℝ) :
    (Rotation.exp (vec 0 0 1) t).act (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z :=
  st_act_Z t x y z

private theorem st_act_negX' (t x y z : ℝ) :
    (Rotation.exp (vec (-1) 0 0) t).act (vec x y z) =
      vec x (cos t * y + sin t * z) (-(sin t * y) + cos t * z) := by
  have : vec (-1) 0 0 = -xAxis := by
    ext i
    fin_cases i <;> simp [vec, xAxis]
  rw [this]
  exact st_act_negX t x y z

private theorem st_vec_sub (a b c d e f : ℝ) :
    vec a b c - vec d e f = vec (a - d) (b - e) (c - f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem st_vec_add (a b c d e f : ℝ) :
    vec a b c + vec d e f = vec (a + d) (b + e) (c + f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem st_vec_smul (r a b c : ℝ) : r • vec a b c = vec (r * a) (r * b) (r * c) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem st_vec_eq {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    vec a b c = vec a' b' c' := by
  rw [ha, hb, hc]

private theorem st_xAxis : xAxis = vec 1 0 0 := rfl
private theorem st_yAxis : yAxis = vec 0 1 0 := rfl
private theorem st_zAxis : zAxis = vec 0 0 1 := rfl

private theorem st_neg_vec (a b c : ℝ) : -vec a b c = vec (-a) (-b) (-c) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem st_revolute_vec (a b c x y z : ℝ) :
    Twist.revolute (vec a b c) (vec x y z) =
      ⟨vec (-(b * z - c * y)) (-(c * x - a * z)) (-(a * y - b * x)), vec a b c⟩ := by
  apply Twist.ext <;> ext i <;> fin_cases i <;>
    simp [Twist.revolute, Vec3.cross, cross_apply, vec]

private theorem st_applyPoint_rev {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) (x : Vec3) :
    (Twist.exp (Twist.revolute ω q) t).applyPoint x = (Rotation.exp ω t).act (x - q) + q :=
  Twist.exp_revolute_applyPoint ω q hω t x

private theorem st_applyVector_rev (ω q : Vec3) (t : ℝ) (v : Vec3) :
    (Twist.exp (Twist.revolute ω q) t).applyVector v = (Rotation.exp ω t).act v := by
  simp [RigidTransform.applyVector, Twist.revolute]

private theorem st_applyPoint_pri (u : Vec3) (t : ℝ) (x : Vec3) :
    (Twist.exp (Twist.prismatic u) t).applyPoint x = x + t • u := by
  rw [Twist.exp_prismatic]
  simp [RigidTransform.applyPoint]

private theorem st_applyVector_pri (u : Vec3) (t : ℝ) (v : Vec3) :
    (Twist.exp (Twist.prismatic u) t).applyVector v = v := by
  rw [Twist.exp_prismatic]
  simp [RigidTransform.applyVector]

/-- The idealized Stanford arm of MLS Example 3.9, Figure 3.14, p. 119: revolute joints about
`+z` and `-x` through `(0, 0, l₀)`, a prismatic joint along `+y`, and wrist joints about `+z`,
`-x`, `+y` through the wrist centre `(0, l₁, l₀)`; the reference tool frame at the wrist centre. -/
def stanfordArm (l₀ l₁ : ℝ) : SerialChain 6 where
  twist := ![Twist.revolute zAxis (vec 0 0 l₀), Twist.revolute (-xAxis) (vec 0 0 l₀),
    Twist.prismatic yAxis, Twist.revolute zAxis (vec 0 l₁ l₀), Twist.revolute (-xAxis) (vec 0 l₁ l₀),
    Twist.revolute yAxis (vec 0 l₁ l₀)]
  toolRef := ⟨1, vec 0 l₁ l₀⟩

/-- **MLS Example 3.9, eq. (3.58), pp. 119–120: the spatial Jacobian of the Stanford arm as
printed.** For all real `l₀, l₁` and joint values, the six columns of the spatial Jacobian are
`ξ₁ = (0, 0, 0, 0, 0, 1)`, `ξ₂' = (l₀ s₁, -l₀ c₁, 0, -c₁, -s₁, 0)`, `ξ₃' = (v₃', 0)` with
`v₃' = (-s₁ c₂, c₁ c₂, -s₂)`, and the wrist twists `(-ωᵢ' × q_w', ωᵢ')` with
`ω₄' = (-s₁ s₂, c₁ s₂, c₂)`, `ω₅' = (-c₁ c₄ + s₁ c₂ s₄, -s₁ c₄ - c₁ c₂ s₄, s₂ s₄)`,
`ω₆' = (-c₅ (s₁ c₂ c₄ + c₁ s₄) + s₁ s₂ s₅, c₅ (c₁ c₂ c₄ - s₁ s₄) - c₁ s₂ s₅, -s₂ c₄ c₅ - c₂ s₅)`
and `q_w' = (-(l₁ + θ₃) s₁ c₂, (l₁ + θ₃) c₁ c₂, l₀ - (l₁ + θ₃) s₂)`. -/
theorem stanfordArm_spatialJacobian (l₀ l₁ : ℝ) (θ : Fin 6 → ℝ) :
    let s := fun i => sin (θ i)
    let c := fun i => cos (θ i)
    let qw := vec (-(l₁ + θ 2) * s 0 * c 1) ((l₁ + θ 2) * c 0 * c 1) (l₀ - (l₁ + θ 2) * s 1)
    (stanfordArm l₀ l₁).spatialJacobian θ =
      ![⟨vec 0 0 0, vec 0 0 1⟩,
        ⟨vec (l₀ * s 0) (-l₀ * c 0) 0, vec (-c 0) (-s 0) 0⟩,
        ⟨vec (-s 0 * c 1) (c 0 * c 1) (-s 1), vec 0 0 0⟩,
        Twist.revolute (vec (-s 0 * s 1) (c 0 * s 1) (c 1)) qw,
        Twist.revolute (vec (-c 0 * c 3 + s 0 * c 1 * s 3) (-s 0 * c 3 - c 0 * c 1 * s 3)
          (s 1 * s 3)) qw,
        Twist.revolute (vec (-c 4 * (s 0 * c 1 * c 3 + c 0 * s 3) + s 0 * s 1 * s 4)
          (c 4 * (c 0 * c 1 * c 3 - s 0 * s 3) - c 0 * s 1 * s 4)
          (-s 1 * c 3 * c 4 - c 1 * s 4)) qw] := by
  intro s c qw
  funext i
  fin_cases i <;>
    simp [SerialChain.spatialJacobian, SerialChain.jointMotions, stanfordArm, List.ofFn_succ,
      Twist.adjoint_revolute, Twist.adjoint_prismatic, st_applyPoint_rev st_norm_zAxis,
      st_applyPoint_rev st_norm_neg_xAxis, st_applyVector_rev, st_applyPoint_pri,
      st_applyVector_pri] <;>
    simp [st_xAxis, st_yAxis, st_zAxis, st_neg_vec, st_vec_sub, st_vec_add, st_vec_smul,
      st_act_negX', st_act_Z', st_revolute_vec, qw, s, c] <;>
    (try apply Twist.ext) <;> (try apply st_vec_eq) <;> ring_nf
  all_goals first
    | exact ⟨trivial, trivial⟩
    | (simp only [Twist.prismatic]
       ext i
       fin_cases i <;> simp [vec])

end Examples

end RoboLean
