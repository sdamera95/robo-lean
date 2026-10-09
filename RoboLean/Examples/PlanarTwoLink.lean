import RoboLean.Kinematics.SerialChain
import RoboLean.Kinematics.Jacobian
import RoboLean.Kinematics.Workspace
import RoboLean.Geometry.ElementaryRotations
import RoboLean.Examples.PlanarVelocity

/-!
# A planar two-revolute chain

A specialization of the SCARA construction of MLS Example 3.1 (printed pp. 87–89,
eq. (3.4)): set `l₀ = θ₃ = θ₄ = 0`, `l₁ = a` and `l₂ = b`, keep the two revolute joints
about `+z` and the zero-pose links along `+y`. MLS does not present this two-link chain as
an example of its own; the specialization is this library's choice (ledger rows K06–K09).

Lean joint `0` is the book's joint `1` and Lean joint `1` is joint `2`, so `q 0 = θ₁` and
`q 1 = θ₂`. Twists use the library order `(v, ω)`, and the product of rigid transforms
applies its right factor first, as in `geometry-conventions.md`.

The contents:

* `planarTwoLink`, the base-frame chain of eq. (3.3) with the twists `ξ₁, ξ₂` and the
  reference tool pose `g_st(0)` of pp. 87–88;
* `planarTwoLinkPosition`, a geometric specification of the tool position built without
  any exponential (the sum of the two rotated link vectors), and its closed form (K06);
* `planarTwoLink_fk`, the product of exponentials equals `Rz(θ₁+θ₂)` and that position,
  eq. (3.4) (K07);
* `planarTwoLinkFrames`, the adjacent-frame description of eq. (3.1) (K02 instance), whose
  forward kinematics is the frame chain `twoLinkPose` of `PlanarVelocity` and agrees with
  `planarTwoLink` through the general theorem `LinkFrameChain.fk_eq_toSerialChain_fk`
  (K05 instance);
* `2π`-periodicity in each angle (K08, p. 84);
* the time derivative of the tool position along a differentiable joint trajectory (K09,
  p. 115);
* the first two columns of the spatial Jacobian of Example 3.8 (p. 118, eq. (3.54),
  p. 116), the spatial velocity of the tool (K10 instance), its agreement with the
  frame-chain derivation of `PlanarVelocity` (MLS p. 60), and the book's check on p. 118
  that the point velocity `(Jˢ θ̇)^ p(θ)` equals `ṗ(θ)` (K12);
* the dextrous workspace of eq. (3.13), p. 95, is empty for this planar arm while its
  reachable workspace is not (K16, planar pilot).

The link lengths `a, b` are arbitrary real numbers: positivity is not assumed and the
algebra does not use it. These are statements about the coordinate model, not about a
physical arm.
-/

noncomputable section

namespace RoboLean.Examples

private theorem norm_zAxis : ‖Rotation.zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [Rotation.zAxis, Fin.sum_univ_succ]

private theorem vec_zero : vec 0 0 0 = 0 := by
  ext i
  fin_cases i <;> rfl

private theorem vec_add_y (a b : ℝ) : vec 0 (a + b) 0 = vec 0 a 0 + vec 0 b 0 := by
  ext i
  fin_cases i <;> simp [vec]

private theorem vec_xy (x y : ℝ) : vec x y 0 = x • vec 1 0 0 + y • vec 0 1 0 := by
  ext i
  fin_cases i <;> simp [vec]

/-- The planar two-revolute chain: MLS Example 3.1 (SCARA, printed pp. 87–88) with
`l₀ = θ₃ = θ₄ = 0`, `l₁ = a`, `l₂ = b`. Both axes are `ω₁ = ω₂ = +z` through the axis points
`q₁ = 0` and `q₂ = (0, l₁, 0)` of p. 88; the reference tool pose is `g_st(0)` of p. 87 with
`l₀ = 0`, the tool at `(0, l₁ + l₂, 0)` with identity orientation. Twists are base-frame
twists in the order `(v, ω)`; the joint space is unrestricted. -/
def planarTwoLink (a b : ℝ) : SerialChain 2 where
  twist := ![Twist.revolute Rotation.zAxis (vec 0 0 0), Twist.revolute Rotation.zAxis (vec 0 a 0)]
  toolRef := ⟨1, vec 0 (a + b) 0⟩

/-- The second joint twist is the printed `ξ₂ = (l₁, 0, 0, 0, 0, 1)` of MLS p. 88, in the
order `(v, ω)` with `l₁ = a`. -/
theorem planarTwoLink_twist_one (a b : ℝ) :
    (planarTwoLink a b).twist 1 = ⟨vec a 0 0, Rotation.zAxis⟩ := by
  apply Twist.ext
  · ext i
    fin_cases i <;>
      simp [planarTwoLink, Twist.revolute, Vec3.cross, cross_apply, Rotation.zAxis, vec]
  · rfl

/-- Both joints of `planarTwoLink` are revolute joints in the sense of MLS p. 87: twists
`(-ω × q, ω)` with unit axis `ω = +z`. -/
theorem planarTwoLink_isRevoluteJoint (a b : ℝ) (i : Fin 2) :
    ((planarTwoLink a b).twist i).IsRevoluteJoint := by
  fin_cases i
  · exact ⟨Rotation.zAxis, vec 0 0 0, norm_zAxis, rfl⟩
  · exact ⟨Rotation.zAxis, vec 0 a 0, norm_zAxis, rfl⟩

/-- **K06, geometric specification (MLS Example 3.1, eq. (3.4), specialized).** The tool
position of the planar two-link arm as the sum of its two link vectors, each rotated about
`+z` by the absolute angle of its link: the first link `(0, a, 0)` by `θ₁ = q 0`, the second
link `(0, b, 0)` by `θ₁ + θ₂ = q 0 + q 1`. The definition uses only rotations of vectors,
not the twist exponential. -/
def planarTwoLinkPosition (a b : ℝ) (q : Fin 2 → ℝ) : Vec3 :=
  (Rotation.zRotation (q 0)).act (vec 0 a 0) + (Rotation.zRotation (q 0 + q 1)).act (vec 0 b 0)

/-- **K06, closed form.** The geometric tool position is
`p(θ) = (-l₁ sin θ₁ - l₂ sin(θ₁+θ₂), l₁ cos θ₁ + l₂ cos(θ₁+θ₂), 0)`, MLS eq. (3.4), p. 89,
with `l₀ = θ₄ = 0`, `l₁ = a`, `l₂ = b`, `θ₁ = q 0`, `θ₂ = q 1`. -/
theorem planarTwoLinkPosition_eq (a b : ℝ) (q : Fin 2 → ℝ) :
    planarTwoLinkPosition a b q =
      vec (-a * Real.sin (q 0) - b * Real.sin (q 0 + q 1))
        (a * Real.cos (q 0) + b * Real.cos (q 0 + q 1)) 0 := by
  ext i
  fin_cases i <;>
    simp [planarTwoLinkPosition, Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, vec] <;> ring

/-- **K07 (MLS eq. (3.4), p. 89, specialized).** The product of exponentials
`exp(ξ̂₁θ₁) exp(ξ̂₂θ₂) g_st(0)` of eq. (3.3) for `planarTwoLink` has rotation
`R(θ) = Rz(θ₁+θ₂)` and translation the geometric position `planarTwoLinkPosition`. The proof
evaluates the two revolute exponentials (`Twist.exp_revolute`), not a closed form placed in
the definition. -/
theorem planarTwoLink_fk (a b : ℝ) (q : Fin 2 → ℝ) :
    (planarTwoLink a b).fk q =
      ⟨Rotation.zRotation (q 0 + q 1), planarTwoLinkPosition a b q⟩ := by
  simp only [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
    List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  have h0 : (planarTwoLink a b).twist 0 = Twist.revolute Rotation.zAxis (vec 0 0 0) := rfl
  have h1 : (planarTwoLink a b).twist (Fin.succ 0) =
      Twist.revolute Rotation.zAxis (vec 0 a 0) := rfl
  rw [h0, h1, Twist.exp_revolute _ _ norm_zAxis, Twist.exp_revolute _ _ norm_zAxis]
  apply RigidTransform.ext
  · simp [planarTwoLink, Rotation.zRotation, Rotation.exp_add]
  · simp only [planarTwoLink, RigidTransform.mul_translation, RigidTransform.mul_rotation,
      vec_zero, map_zero, sub_zero, add_zero, vec_add_y, map_add, map_sub,
      planarTwoLinkPosition]
    simp only [Rotation.zRotation, Rotation.exp_add, Rotation.act_mul, Fin.succ_zero_eq_one]
    abel

/-- The rotation part of K07: `R(θ) = Rz(θ₁+θ₂)`, MLS eq. (3.4), p. 89, specialized to
`θ₃ = 0`. -/
theorem planarTwoLink_fk_rotation (a b : ℝ) (q : Fin 2 → ℝ) :
    ((planarTwoLink a b).fk q).rotation = Rotation.zRotation (q 0 + q 1) := by
  rw [planarTwoLink_fk]

/-- The translation part of K07 in closed trigonometric form,
`p(θ) = (-l₁ sin θ₁ - l₂ sin(θ₁+θ₂), l₁ cos θ₁ + l₂ cos(θ₁+θ₂), 0)`, MLS eq. (3.4), p. 89,
with `l₀ = θ₄ = 0`, `l₁ = a`, `l₂ = b`. -/
theorem planarTwoLink_fk_translation (a b : ℝ) (q : Fin 2 → ℝ) :
    ((planarTwoLink a b).fk q).translation =
      vec (-a * Real.sin (q 0) - b * Real.sin (q 0 + q 1))
        (a * Real.cos (q 0) + b * Real.cos (q 0 + q 1)) 0 := by
  rw [planarTwoLink_fk, planarTwoLinkPosition_eq]

/-- **K02 instance (MLS eq. (3.1), p. 85).** The planar two-link arm described by adjacent
link frames: base `S = L₀`, link frames `L₁, L₂` and tool `T`. Each joint twist is written
in its proximal link frame (both axes `+z`; joint 2 passes through `(0, a, 0)` of `L₁`), the
reference relative poses are `g_{S L₁}(0) = 1` and `g_{L₁ L₂}(0) = (I, (0, a, 0))`, and the
tool offset is `g_{L₂ T} = (I, (0, b, 0))`. Twists are in the order `(v, ω)`. -/
def planarTwoLinkFrames (a b : ℝ) : LinkFrameChain 2 where
  jointTwist :=
    ![Twist.revolute Rotation.zAxis (vec 0 0 0), Twist.revolute Rotation.zAxis (vec 0 a 0)]
  linkRef := ![1, ⟨1, vec 0 a 0⟩]
  toolOffset := ⟨1, vec 0 b 0⟩

/-- The adjacent-frame forward kinematics of eq. (3.1), MLS p. 85, for `planarTwoLinkFrames`
is the two-joint frame chain `twoLinkPose 0 a θ₁ θ₂` of `PlanarVelocity` (MLS Example 2.6
with `l₀ = 0`), followed by the tool offset `(I, (0, b, 0))`. -/
theorem planarTwoLinkFrames_fk (a b : ℝ) (q : Fin 2 → ℝ) :
    (planarTwoLinkFrames a b).fk q =
      twoLinkPose 0 a (q 0) (q 1) * ⟨1, vec 0 b 0⟩ := by
  simp only [LinkFrameChain.fk, LinkFrameChain.relative, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, mul_one]
  have h0 : (planarTwoLinkFrames a b).jointTwist 0 =
      Twist.revolute Rotation.zAxis (vec 0 0 0) := rfl
  have h1 : (planarTwoLinkFrames a b).jointTwist (Fin.succ 0) =
      Twist.revolute Rotation.zAxis (vec 0 a 0) := rfl
  have l0 : (planarTwoLinkFrames a b).linkRef 0 = 1 := rfl
  have l1 : (planarTwoLinkFrames a b).linkRef (Fin.succ 0) = ⟨1, vec 0 a 0⟩ := rfl
  rw [h0, h1, l0, l1, Twist.exp_revolute _ _ norm_zAxis, Twist.exp_revolute _ _ norm_zAxis,
    twoLinkPose_factors]
  apply RigidTransform.ext
  · simp [planarTwoLinkFrames, Rotation.zRotation]
  · simp [planarTwoLinkFrames, Rotation.zRotation, vec_zero]

/-- The base-frame chain derived from `planarTwoLinkFrames` by moving each joint twist to
the base frame (`ξᵢ = Ad_{g_{S Lᵢ}(0)} ζᵢ`, MLS eq. (2.58), p. 55, and p. 87) and composing the
reference poses into `g_st(0)` is exactly `planarTwoLink`. -/
theorem planarTwoLinkFrames_toSerialChain (a b : ℝ) :
    (planarTwoLinkFrames a b).toSerialChain = planarTwoLink a b := by
  unfold LinkFrameChain.toSerialChain planarTwoLink
  congr 1
  · funext i
    fin_cases i <;>
      simp [LinkFrameChain.refLinkPose, planarTwoLinkFrames]
  · simp only [planarTwoLinkFrames, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
      List.prod_nil]
    apply RigidTransform.ext
    · simp
    · simp [vec_add_y, add_comm]

/-- **K05 instance (MLS eqs. (3.1) and (3.3), pp. 85–87).** The product-of-exponentials
forward kinematics of `planarTwoLink` equals the adjacent-frame composition
`twoLinkPose 0 a θ₁ θ₂ * (I, (0, b, 0))`. The proof applies the general theorem
`LinkFrameChain.fk_eq_toSerialChain_fk` to `planarTwoLinkFrames`; it does not recompute
either side. -/
theorem planarTwoLink_fk_eq_twoLinkPose (a b : ℝ) (q : Fin 2 → ℝ) :
    (planarTwoLink a b).fk q = twoLinkPose 0 a (q 0) (q 1) * ⟨1, vec 0 b 0⟩ := by
  rw [← planarTwoLinkFrames_toSerialChain, ← LinkFrameChain.fk_eq_toSerialChain_fk,
    planarTwoLinkFrames_fk]

/-- **K08 (MLS p. 84).** The forward kinematics of `planarTwoLink` is `2π`-periodic in each
joint angle: shifting `θᵢ` by any integer multiple `kᵢ` of `2π` leaves the tool pose
unchanged. This is `SerialChain.fk_add_int_mul_two_pi` with both joints revolute. -/
theorem planarTwoLink_fk_add_int_mul_two_pi (a b : ℝ) (q : Fin 2 → ℝ) (k : Fin 2 → ℤ) :
    (planarTwoLink a b).fk (fun i => q i + k i * (2 * Real.pi)) = (planarTwoLink a b).fk q :=
  SerialChain.fk_add_int_mul_two_pi _ q k fun i _ => planarTwoLink_isRevoluteJoint a b i

/-- **K09 (MLS p. 115, differentiating a forward kinematics map `g : ℝⁿ → ℝᵖ`).**
Along a joint trajectory `s ↦ q s` with joint rates `q' i` at time `t`, the tool position of
`planarTwoLink` has time derivative
`(-a cos θ₁ θ̇₁ - b cos(θ₁+θ₂)(θ̇₁+θ̇₂), -a sin θ₁ θ̇₁ - b sin(θ₁+θ₂)(θ̇₁+θ̇₂), 0)`.
This is the position Jacobian `∂p/∂θ` applied to the joint rates, not the spatial twist
Jacobian of eq. (3.54), p. 116: the check of Example 3.8, p. 118, compares `ṗ(θ)` with the
point velocity `(J θ̇)^ p(θ)`, which includes `ω × p` (ledger K09 and K12). -/
theorem hasDerivAt_planarTwoLink_translation (a b : ℝ) {q : ℝ → Fin 2 → ℝ} {q' : Fin 2 → ℝ}
    {t : ℝ} (hq : ∀ i, HasDerivAt (fun s => q s i) (q' i) t) :
    HasDerivAt (fun s => ((planarTwoLink a b).fk (q s)).translation)
      (vec (-a * Real.cos (q t 0) * q' 0 - b * Real.cos (q t 0 + q t 1) * (q' 0 + q' 1))
        (-a * Real.sin (q t 0) * q' 0 - b * Real.sin (q t 0 + q t 1) * (q' 0 + q' 1)) 0) t := by
  have h0 := hq 0
  have h01 : HasDerivAt (fun s => q s 0 + q s 1) (q' 0 + q' 1) t := (hq 0).add (hq 1)
  have hx : HasDerivAt (fun s => -a * Real.sin (q s 0) - b * Real.sin (q s 0 + q s 1))
      (-a * Real.cos (q t 0) * q' 0 - b * Real.cos (q t 0 + q t 1) * (q' 0 + q' 1)) t := by
    convert (h0.sin.const_mul (-a)).sub (h01.sin.const_mul b) using 1
    ring
  have hy : HasDerivAt (fun s => a * Real.cos (q s 0) + b * Real.cos (q s 0 + q s 1))
      (-a * Real.sin (q t 0) * q' 0 - b * Real.sin (q t 0 + q t 1) * (q' 0 + q' 1)) t := by
    convert (h0.cos.const_mul a).add (h01.cos.const_mul b) using 1
    ring
  convert (hx.smul_const (vec 1 0 0)).add (hy.smul_const (vec 0 1 0)) using 1
  · funext s
    rw [Pi.add_apply, planarTwoLink_fk_translation, vec_xy]
  · exact vec_xy _ _

/-! ### Spatial Jacobian, spatial velocity and the check of Example 3.8 -/

/-- The first column of the spatial Jacobian of `planarTwoLink` is the first joint twist
`ξ₁ = (0, 0, 0, 0, 0, 1)`, the first printed column of `Jˢ` in MLS Example 3.8, p. 118
(eq. (3.54), p. 116). Twist order `(v, ω)`. -/
theorem planarTwoLink_spatialJacobian_zero (a b : ℝ) (q : Fin 2 → ℝ) :
    (planarTwoLink a b).spatialJacobian q 0 = ⟨vec 0 0 0, vec 0 0 1⟩ := by
  rw [SerialChain.spatialJacobian_zero]
  apply Twist.ext <;> ext i <;> fin_cases i <;>
    simp [planarTwoLink, Twist.revolute, Vec3.cross, cross_apply, Rotation.zAxis, vec]

/-- The second column of the spatial Jacobian of `planarTwoLink`,
`ξ₂' = Ad_{exp(ξ̂₁θ₁)} ξ₂ = (l₁ cos θ₁, l₁ sin θ₁, 0, 0, 0, 1)` with `l₁ = a`: the second
printed column of `Jˢ` in MLS Example 3.8, p. 118 (eq. (3.54), p. 116). It is computed from
the definition, the adjoint of the first joint exponential applied to `ξ₂`. Twist order
`(v, ω)`. -/
theorem planarTwoLink_spatialJacobian_one (a b : ℝ) (q : Fin 2 → ℝ) :
    (planarTwoLink a b).spatialJacobian q 1 =
      ⟨vec (a * Real.cos (q 0)) (a * Real.sin (q 0)) 0, vec 0 0 1⟩ := by
  have hg : ((planarTwoLink a b).jointMotions q).take 1 =
      [Twist.exp (Twist.revolute Rotation.zAxis (vec 0 0 0)) (q 0)] := by
    simp [SerialChain.jointMotions, List.ofFn_succ, planarTwoLink]
  have hz : Rotation.exp Rotation.zAxis (q 0) = Rotation.zRotation (q 0) := rfl
  change Twist.adjoint (((planarTwoLink a b).jointMotions q).take 1).prod
      ((planarTwoLink a b).twist 1) = _
  rw [hg, List.prod_singleton, Twist.exp_revolute _ _ norm_zAxis, planarTwoLink_twist_one, hz,
    vec_zero, map_zero, sub_zero]
  apply Twist.ext <;> ext i <;> fin_cases i <;>
    simp [Twist.adjoint, Rotation.act_apply,
      Rotation.zRotation_val, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Vec3.cross,
      Rotation.zAxis, vec, mul_comm]

/-- **K10 instance (MLS eqs. (3.51)–(3.54), pp. 115–116; Example 3.8, p. 118).** Along a
joint trajectory with rates `θ̇ = q'` at time `t`, the actual spatial velocity
`V̂ˢ = ġ g⁻¹` of the tool pose of `planarTwoLink`, for any derivative `D` of the homogeneous
pose, is `θ̇₁ ξ₁ + θ̇₂ ξ₂'` with the columns printed on p. 118 (`l₁ = a`). The proof applies
the general `SerialChain.spatialVelocity_fk`; a derivative `D` exists by
`SerialChain.hasDerivAt_fk_toHomogeneous`. Twist order `(v, ω)`. -/
theorem planarTwoLink_spatialVelocity (a b : ℝ) {q : ℝ → Fin 2 → ℝ} {q' : Fin 2 → ℝ} {t : ℝ}
    (hq : ∀ i, HasDerivAt (fun s => q s i) (q' i) t) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => ((planarTwoLink a b).fk (q s)).toHomogeneous) D t) :
    RigidTransform.spatialVelocity (fun s => (planarTwoLink a b).fk (q s)) D t hD =
      q' 0 • (⟨vec 0 0 0, vec 0 0 1⟩ : Twist) +
        q' 1 • (⟨vec (a * Real.cos (q t 0)) (a * Real.sin (q t 0)) 0, vec 0 0 1⟩ : Twist) := by
  rw [SerialChain.spatialVelocity_fk _ hq hD, Fin.sum_univ_two,
    planarTwoLink_spatialJacobian_zero, planarTwoLink_spatialJacobian_one]

/-- Cross-check of two independent derivations. The spatial velocity of `planarTwoLink`
from the product-of-exponentials Jacobian (MLS Example 3.8, p. 118) equals the spatial
velocity of the frame chain `twoLinkPose 0 a θ₁ θ₂` of `PlanarVelocity`, derived by the
product rule from MLS Example 2.6 (p. 60, here with `l₀ = 0`). Both sides are rewritten by
their own theorems (`planarTwoLink_spatialVelocity` and `twoLinkPose_spatialVelocity`), so
the agreement of the two results is what is checked. The tool offset `(I, (0, b, 0))` does
not change the spatial velocity. -/
theorem planarTwoLink_spatialVelocity_eq_twoLinkPose (a b : ℝ) {q : ℝ → Fin 2 → ℝ}
    {q' : Fin 2 → ℝ} {t : ℝ} (hq : ∀ i, HasDerivAt (fun s => q s i) (q' i) t)
    {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => ((planarTwoLink a b).fk (q s)).toHomogeneous) D t) :
    RigidTransform.spatialVelocity (fun s => (planarTwoLink a b).fk (q s)) D t hD =
      RigidTransform.spatialVelocity (fun s => twoLinkPose 0 a (q s 0) (q s 1))
        (twoLinkPoseDerivative 0 a (q t 0) (q t 1) (q' 0) (q' 1)) t
        (hasDerivAt_twoLinkPose 0 a (hq 0) (hq 1)) := by
  rw [planarTwoLink_spatialVelocity a b hq hD, twoLinkPose_spatialVelocity 0 a (hq 0) (hq 1)]

/-- **K12 check, arithmetic form (MLS Example 3.8, p. 118).** For every configuration `θ = q`
and joint rates `θ̇ = q'`, the velocity of the tool origin computed from the spatial
Jacobian, `ωˢ × p(θ) + vˢ` with `(vˢ, ωˢ) = Jˢ(θ) θ̇` (the formula `(Jˢ θ̇)^ p(θ)` of p. 118),
equals the position derivative of K09,
`(-a cos θ₁ θ̇₁ - b cos(θ₁+θ₂)(θ̇₁+θ̇₂), -a sin θ₁ θ̇₁ - b sin(θ₁+θ₂)(θ̇₁+θ̇₂), 0)`. The term
`ωˢ × p` is needed; `vˢ` alone is not `ṗ`. -/
theorem planarTwoLink_point_velocity (a b : ℝ) (q q' : Fin 2 → ℝ) :
    Vec3.cross (∑ i, q' i • (planarTwoLink a b).spatialJacobian q i).angular
        ((planarTwoLink a b).fk q).translation +
      (∑ i, q' i • (planarTwoLink a b).spatialJacobian q i).linear =
      vec (-a * Real.cos (q 0) * q' 0 - b * Real.cos (q 0 + q 1) * (q' 0 + q' 1))
        (-a * Real.sin (q 0) * q' 0 - b * Real.sin (q 0 + q 1) * (q' 0 + q' 1)) 0 := by
  rw [Fin.sum_univ_two, planarTwoLink_spatialJacobian_zero, planarTwoLink_spatialJacobian_one,
    planarTwoLink_fk_translation]
  ext i
  fin_cases i <;>
    simp [Vec3.cross, cross_apply, vec] <;> ring

/-- **K12, the check of MLS Example 3.8, p. 118.** The derivative of the tool position of
`planarTwoLink` along a joint trajectory, obtained from the general Jacobian result
`SerialChain.hasDerivAt_fk_translation` (`ṗ = ωˢ × p + vˢ` with `(vˢ, ωˢ) = Jˢ(θ) θ̇`,
MLS p. 117) and `planarTwoLink_point_velocity`. It reaches the same vector as the direct
derivative `hasDerivAt_planarTwoLink_translation` (K09) without using it; the point velocity
includes the `ω × p` term. -/
theorem hasDerivAt_planarTwoLink_translation_of_jacobian (a b : ℝ) {q : ℝ → Fin 2 → ℝ}
    {q' : Fin 2 → ℝ} {t : ℝ} (hq : ∀ i, HasDerivAt (fun s => q s i) (q' i) t) :
    HasDerivAt (fun s => ((planarTwoLink a b).fk (q s)).translation)
      (vec (-a * Real.cos (q t 0) * q' 0 - b * Real.cos (q t 0 + q t 1) * (q' 0 + q' 1))
        (-a * Real.sin (q t 0) * q' 0 - b * Real.sin (q t 0 + q t 1) * (q' 0 + q' 1)) 0) t := by
  have h := (planarTwoLink a b).hasDerivAt_fk_translation hq
  rwa [planarTwoLink_point_velocity] at h

/-! ### Workspaces (MLS eqs. (3.12)–(3.13), p. 95) -/

/-- **K16, planar pilot (MLS eq. (3.13), p. 95).** The dextrous workspace of `planarTwoLink`
is empty for every admissible set `Q`: every tool rotation is `Rz(θ₁+θ₂)`, which fixes
`+z`, while the dextrous workspace asks for every rotation of `SO(3)`, including the quarter
turn `Rx(π/2)`. The three-dimensional definition of eq. (3.13) is therefore empty for this
planar arm because it cannot realize arbitrary orientations (ledger K16 divergence note);
no planar-orientation variant is defined here. -/
theorem planarTwoLink_dextrousWorkspace_eq_empty (a b : ℝ) (Q : Set (Fin 2 → ℝ)) :
    (planarTwoLink a b).dextrousWorkspace Q = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  obtain ⟨θ, -, h⟩ := hp (Rotation.xRotation (Real.pi / 2))
  have hR := congrArg (fun g : RigidTransform => g.rotation.val 2 2) h
  simp [planarTwoLink_fk_rotation, Rotation.zRotation_val, Rotation.xMatrix] at hR

/-- The reachable workspace of `planarTwoLink` (MLS eq. (3.12), p. 95) contains the
reference tool position `(0, a + b, 0)` whenever the reference configuration `θ = 0` is
admissible (`g_st(0)`, p. 87), so for such `Q` it differs from the empty dextrous workspace
(`planarTwoLink_dextrousWorkspace_eq_empty`). -/
theorem planarTwoLink_reachableWorkspace_nonempty (a b : ℝ) (Q : Set (Fin 2 → ℝ))
    (h : (0 : Fin 2 → ℝ) ∈ Q) :
    vec 0 (a + b) 0 ∈ (planarTwoLink a b).reachableWorkspace Q :=
  SerialChain.toolRef_translation_mem_reachableWorkspace (c := planarTwoLink a b) h

end RoboLean.Examples
