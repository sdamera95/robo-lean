import RoboLean.Kinematics.SerialChain
import RoboLean.Geometry.ElementaryRotations
import RoboLean.Geometry.Homogeneous

/-!
# Denavit–Hartenberg parameters and the product of exponentials

MLS §3.2.3, printed pp. 93–95. The transform between adjacent link frames in
Denavit–Hartenberg form is the printed `4 × 4` matrix of p. 93 in the four parameters
`(αᵢ, aᵢ, dᵢ, φᵢ)`; the forward kinematics is their product (3.6). For a revolute joint the
joint variable enters `φᵢ`, for a prismatic joint it enters `dᵢ` (p. 93). Here the joint
variable is added to a stored reference value of that parameter, so that `θ = 0` is the
configuration with the stored parameters; a stored value `0` is the book's identification
`φᵢ = θᵢ` (or `dᵢ = θᵢ`).

The matrix is a proper rigid transform with rotation `Rz(φ) Rx(α)` and translation
`(a cos φ, a sin φ, d)`. A change of the joint variable is a rotation about, or a
translation along, the `z`-axis of the proximal frame applied on the left, so that each
adjacent transform has the form (3.7), `g_{lᵢ₋₁ lᵢ}(θᵢ) = exp(ξ̂ᵢ₋₁,ᵢ θᵢ) g_{lᵢ₋₁ lᵢ}(0)`, with
`ξᵢ₋₁,ᵢ = (0, 0, 0, 0, 0, 1)` (revolute) or `(0, 0, 1, 0, 0, 0)` (prismatic). A chain of
such transforms is therefore an adjacent-frame chain (`LinkFrameChain`), and its forward
kinematics (3.6) equals the product-of-exponentials forward kinematics (3.3) with the
base-frame twists (3.10), `ξᵢ = Ad_{g_{l₀ lᵢ₋₁}(0)} ξᵢ₋₁,ᵢ`.

Conventions: twists `(v, ω)`, homogeneous matrices `[R p; 0 1]` indexed by `Fin 3 ⊕ Fin 1`,
Lean joint `i` is the book's joint `i + 1`, all parameters arbitrary reals.
-/

noncomputable section

open Real

namespace RoboLean

private theorem norm_zAxis_dh : ‖Rotation.zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [Rotation.zAxis, Fin.sum_univ_succ]

namespace RigidTransform

/-- The Denavit–Hartenberg transform between adjacent link frames, MLS p. 93 (the matrix
after (3.6)): rotation `Rz(φ) Rx(α)` and translation `(a cos φ, a sin φ, d)`, in the
parameters `α` (twist angle), `a` (link length), `d` (link offset) and `φ` (joint angle). -/
def denavitHartenberg (α a d φ : ℝ) : RigidTransform :=
  ⟨Rotation.zRotation φ * Rotation.xRotation α, WithLp.toLp 2 ![a * cos φ, a * sin φ, d]⟩

/-- The printed Denavit–Hartenberg matrix of MLS p. 93 as data, in homogeneous coordinates
`[R p; 0 1]`:
`[[cos φ, −sin φ cos α, sin φ sin α, a cos φ], [sin φ, cos φ cos α, −cos φ sin α, a sin φ],
[0, sin α, cos α, d], [0, 0, 0, 1]]`. -/
def denavitHartenbergMatrix (α a d φ : ℝ) : HomogeneousMatrix :=
  Matrix.fromBlocks
    !![cos φ, -sin φ * cos α, sin φ * sin α;
      sin φ, cos φ * cos α, -cos φ * sin α;
      0, sin α, cos α]
    (Matrix.of fun i _ => ![a * cos φ, a * sin φ, d] i) 0 1

/-- **MLS p. 93.** The homogeneous matrix of the Denavit–Hartenberg transform is the printed
matrix, entry by entry, for all real `α, a, d, φ`. -/
theorem toHomogeneous_denavitHartenberg (α a d φ : ℝ) :
    (denavitHartenberg α a d φ).toHomogeneous = denavitHartenbergMatrix α a d φ := by
  simp only [toHomogeneous, denavitHartenberg, denavitHartenbergMatrix]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rotation.zRotation_val, Rotation.xMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- **MLS p. 93 ("only four parameters").** The Denavit–Hartenberg transform is the composite
of a rotation by `φ` about `z`, a translation by `d` along `z`, a translation by `a` along `x`
and a rotation by `α` about `x`, in this order from the left. This factorization is not
printed on p. 93; it is the standard reading of the four parameters (cited there to Spong and
Vidyasagar). -/
theorem denavitHartenberg_eq_mul (α a d φ : ℝ) :
    denavitHartenberg α a d φ =
      ⟨Rotation.zRotation φ, 0⟩ * ⟨1, d • Rotation.zAxis⟩ * ⟨1, a • Rotation.xAxis⟩ *
        ⟨Rotation.xRotation α, 0⟩ := by
  apply RigidTransform.ext
  · simp [denavitHartenberg]
  · ext i
    fin_cases i <;>
      simp [denavitHartenberg, Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, Rotation.zAxis, Rotation.xAxis]

/-- **MLS p. 93 with eq. (3.7), p. 94, revolute joint.** Adding `θ` to the joint angle `φ`
applies the revolute joint motion about the `z`-axis of the proximal frame on the left:
`g(θ + φ) = exp(ξ̂θ) g(φ)` with `ξ = (0, 0, 0, 0, 0, 1)`, the revolute twist of the `z`-axis
through the origin (MLS p. 87). -/
theorem denavitHartenberg_add_angle (α a d φ θ : ℝ) :
    denavitHartenberg α a d (θ + φ) =
      Twist.exp (Twist.revolute Rotation.zAxis 0) θ * denavitHartenberg α a d φ := by
  rw [Twist.exp_revolute _ _ norm_zAxis_dh,
    show Rotation.exp Rotation.zAxis θ = Rotation.zRotation θ from rfl]
  apply RigidTransform.ext
  · simp only [denavitHartenberg, mul_rotation]
    rw [← mul_assoc]
    congr 1
    simp only [Rotation.zRotation]
    rw [Rotation.exp_add]
  · ext i
    fin_cases i <;>
      simp [denavitHartenberg, Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, cos_add, sin_add] <;> ring

/-- **MLS p. 93 with eq. (3.7), p. 94, prismatic joint.** Adding `θ` to the link offset `d`
applies the prismatic joint motion along the `z`-axis of the proximal frame on the left:
`g(θ + d) = exp(ξ̂θ) g(d)` with `ξ = (0, 0, 1, 0, 0, 0)` (MLS p. 87). -/
theorem denavitHartenberg_add_offset (α a d φ θ : ℝ) :
    denavitHartenberg α a (θ + d) φ =
      Twist.exp (Twist.prismatic Rotation.zAxis) θ * denavitHartenberg α a d φ := by
  rw [Twist.exp_prismatic]
  apply RigidTransform.ext
  · simp [denavitHartenberg]
  · ext i
    fin_cases i <;> simp [denavitHartenberg, Rotation.zAxis]
    ring

end RigidTransform

/-- A serial chain described by Denavit–Hartenberg parameters, MLS p. 93, eq. (3.6). Lean
joint `i` connects link frame `Lᵢ` to `Lᵢ₊₁` (the book's `l_{i}` to `l_{i+1}`, with `L₀ = S`),
its transform is `denavitHartenberg (α i) (a i) (d i) (φ i)` with the joint variable added to
`φ i` when `revolute i` holds and to `d i` otherwise, and `toolOffset` is `g_{lₙ t}`. The
stored `φ i` or `d i` of the moving parameter is its value at `θ = 0`. -/
structure DenavitHartenbergChain (n : ℕ) where
  /-- The twist angles `αᵢ` (MLS p. 93). -/
  α : Fin n → ℝ
  /-- The link lengths `aᵢ` (MLS p. 93). -/
  a : Fin n → ℝ
  /-- The link offsets `dᵢ`; for a prismatic joint the value at `θ = 0` (MLS p. 93). -/
  d : Fin n → ℝ
  /-- The joint angles `φᵢ`; for a revolute joint the value at `θ = 0` (MLS p. 93). -/
  φ : Fin n → ℝ
  /-- Whether joint `i` is revolute (joint variable in `φᵢ`) or prismatic (in `dᵢ`),
  MLS p. 93. -/
  revolute : Fin n → Bool
  /-- The fixed tool transform `g_{lₙ t}` of eq. (3.6) (MLS p. 93). -/
  toolOffset : RigidTransform

namespace DenavitHartenbergChain

variable {n : ℕ}

/-- The adjacent link transform `g_{lᵢ lᵢ₊₁}(θᵢ)` of a Denavit–Hartenberg chain, MLS p. 93:
the joint variable added to `φᵢ` (revolute) or to `dᵢ` (prismatic). -/
def link (c : DenavitHartenbergChain n) (i : Fin n) (t : ℝ) : RigidTransform :=
  if c.revolute i then RigidTransform.denavitHartenberg (c.α i) (c.a i) (c.d i) (t + c.φ i)
  else RigidTransform.denavitHartenberg (c.α i) (c.a i) (t + c.d i) (c.φ i)

/-- The forward kinematics of a Denavit–Hartenberg chain, MLS eq. (3.6), p. 93:
`g_st(θ) = g_{l₀ l₁}(θ₁) g_{l₁ l₂}(θ₂) ⋯ g_{lₙ₋₁ lₙ}(θₙ) g_{lₙ t}`. -/
def fk (c : DenavitHartenbergChain n) (θ : Fin n → ℝ) : RigidTransform :=
  (List.ofFn fun i => c.link i (θ i)).prod * c.toolOffset

/-- The relative joint twist `ξᵢ₋₁,ᵢ` of a Denavit–Hartenberg joint in its proximal link frame,
MLS p. 94, eq. (3.7): `(0, 0, 0, 0, 0, 1)` for a revolute joint (the `z`-axis through the
origin) and `(0, 0, 1, 0, 0, 0)` for a prismatic joint. -/
def jointTwist (c : DenavitHartenbergChain n) (i : Fin n) : Twist :=
  if c.revolute i then Twist.revolute Rotation.zAxis 0 else Twist.prismatic Rotation.zAxis

/-- The adjacent-frame chain of a Denavit–Hartenberg chain, MLS p. 94, eqs. (3.7)–(3.8): joint
twists `ξᵢ₋₁,ᵢ` (`jointTwist`), reference transforms `g_{lᵢ₋₁ lᵢ}(0)` (the Denavit–Hartenberg
transform at the stored parameters) and the same tool offset. -/
def toLinkFrameChain (c : DenavitHartenbergChain n) : LinkFrameChain n where
  jointTwist := c.jointTwist
  linkRef i := RigidTransform.denavitHartenberg (c.α i) (c.a i) (c.d i) (c.φ i)
  toolOffset := c.toolOffset

/-- **MLS eq. (3.7), p. 94.** Every adjacent Denavit–Hartenberg transform has the form
`g_{lᵢ₋₁ lᵢ}(θᵢ) = exp(ξ̂ᵢ₋₁,ᵢ θᵢ) g_{lᵢ₋₁ lᵢ}(0)`, for every real joint variable. -/
theorem link_eq_relative (c : DenavitHartenbergChain n) (i : Fin n) (t : ℝ) :
    c.link i t = c.toLinkFrameChain.relative i t := by
  simp only [link, LinkFrameChain.relative, toLinkFrameChain, jointTwist]
  cases c.revolute i
  · exact RigidTransform.denavitHartenberg_add_offset _ _ _ _ _
  · exact RigidTransform.denavitHartenberg_add_angle _ _ _ _ _

/-- **MLS eqs. (3.6) and (3.8), pp. 93–94.** The Denavit–Hartenberg forward kinematics is the
adjacent-frame forward kinematics of `toLinkFrameChain`, for every real joint vector. -/
theorem fk_eq_linkFrameChain_fk (c : DenavitHartenbergChain n) (θ : Fin n → ℝ) :
    c.fk θ = c.toLinkFrameChain.fk θ := by
  simp only [fk, LinkFrameChain.fk, link_eq_relative]
  rfl

/-- **MLS eqs. (3.6), (3.8), (3.10) and (3.3), pp. 87–94: the Denavit–Hartenberg forward
kinematics as a product of exponentials.** For every real joint vector, `g_st(θ)` of (3.6)
equals `exp(ξ̂₁θ₁) ⋯ exp(ξ̂ₙθₙ) g_st(0)` for the base-frame twists
`ξᵢ = Ad_{g_{l₀ lᵢ₋₁}(0)} ξᵢ₋₁,ᵢ` of (3.10) and `g_st(0) = g_{l₀ lₙ}(0) g_{lₙ t}`
(`LinkFrameChain.toSerialChain`). -/
theorem fk_eq_serialChain_fk (c : DenavitHartenbergChain n) (θ : Fin n → ℝ) :
    c.fk θ = c.toLinkFrameChain.toSerialChain.fk θ := by
  rw [fk_eq_linkFrameChain_fk, LinkFrameChain.fk_eq_toSerialChain_fk]

/-- **MLS p. 94, eq. (3.10), revolute joints.** The base-frame twist of a revolute
Denavit–Hartenberg joint is a revolute joint twist (unit axis `R_{l₀ lᵢ₋₁}(0) z` through the
origin of `lᵢ₋₁`). -/
theorem serialChain_twist_isRevoluteJoint (c : DenavitHartenbergChain n) (i : Fin n)
    (hi : c.revolute i = true) : (c.toLinkFrameChain.toSerialChain.twist i).IsRevoluteJoint := by
  apply LinkFrameChain.toSerialChain_isRevoluteJoint
  exact ⟨Rotation.zAxis, 0, norm_zAxis_dh, by simp [toLinkFrameChain, jointTwist, hi]⟩

/-- **MLS p. 94, eq. (3.10), prismatic joints.** The base-frame twist of a prismatic
Denavit–Hartenberg joint is a prismatic joint twist (unit direction `R_{l₀ lᵢ₋₁}(0) z`). -/
theorem serialChain_twist_isPrismaticJoint (c : DenavitHartenbergChain n) (i : Fin n)
    (hi : c.revolute i = false) :
    (c.toLinkFrameChain.toSerialChain.twist i).IsPrismaticJoint := by
  apply LinkFrameChain.toSerialChain_isPrismaticJoint
  exact ⟨Rotation.zAxis, norm_zAxis_dh, by simp [toLinkFrameChain, jointTwist, hi]⟩

end DenavitHartenbergChain

end RoboLean
