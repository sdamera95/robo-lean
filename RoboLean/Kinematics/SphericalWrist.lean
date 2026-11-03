import RoboLean.Kinematics.Workspace
import RoboLean.Kinematics.SphericalWristAngles

/-!
# The workspace of a manipulator with a spherical wrist

MLS Chapter 3, §2.4, printed p. 96: "a spherical wrist consists of three orthogonal revolute axes
which intersect at a point. If the end-effector frame is placed at the origin of the wrist axes,
then the spherical wrist can be used to achieve any orientation at a given end-effector position.
Hence, for a manipulator with a spherical wrist, the dextrous workspace is equal to the reachable
workspace, `W_D = W_R`. Furthermore, the complete workspace for the end-effector satisfies
`W = W_R × SO(3)`."

Model. A chain of `n + 3` joints whose last three joints (Lean indices `Fin.natAdd n i`) are
revolute with unit axes `ω₀, ω₁, ω₂` through the tool-frame origin `p_st(0)` of the reference
configuration, with `ω₀ ⊥ ω₁` and `ω₁ ⊥ ω₂` (`SerialChain.HasSphericalWrist`). Every axis point of
such an axis gives the same twist, so placing the axis point at `p_st(0)` is the book's "end-effector
frame at the origin of the wrist axes". The third orthogonality `ω₀ ⊥ ω₂` of "three orthogonal
axes" is not needed and not assumed. The joint space is unrestricted (`Set.univ`); with joint
limits on the wrist the statements fail in general.

Results: the forward kinematics splits as the arm's product of exponentials times the pose
`(e^{ω̂₀θ₀} e^{ω̂₁θ₁} e^{ω̂₂θ₂} R_st(0), p_st(0))`, so the position does not depend on the wrist
angles; `W_D = W_R` and `W = {g : p(g) ∈ W_R}`, the latter being `W_R × SO(3)` as a set of poses.
-/

noncomputable section

namespace RoboLean
namespace SerialChain

variable {n : ℕ}

/-- **MLS p. 96: a spherical wrist at the end of the chain, with the end-effector frame at the wrist
centre.** The last three joints of a chain of `n + 3` joints are revolute with unit axes `ω i`
through the reference tool position `p_st(0)` (the translation of `g_st(0)`), and consecutive axes
are orthogonal: `ω₀ ⊥ ω₁`, `ω₁ ⊥ ω₂`. Lean wrist joint `i` is the chain's joint `n + i`. -/
structure HasSphericalWrist (c : SerialChain (n + 3)) (ω : Fin 3 → Vec3) : Prop where
  /-- The wrist axes are unit vectors. -/
  norm_axis : ∀ i, ‖ω i‖ = 1
  /-- The first two wrist axes are orthogonal. -/
  inner_zero_one : inner ℝ (ω 0) (ω 1) = 0
  /-- The last two wrist axes are orthogonal. -/
  inner_one_two : inner ℝ (ω 1) (ω 2) = 0
  /-- The wrist joints are revolute about axes through the reference tool position. -/
  twist_eq : ∀ i, c.twist (Fin.natAdd n i) = Twist.revolute (ω i) c.toolRef.translation

/-- The product of the first `n` joint motions `e^{ξ̂₁θ₁} ⋯ e^{ξ̂ₙθₙ}` of a chain of `n + 3`
joints (MLS eq. (3.3), p. 87, restricted to the arm before the wrist). -/
def armPoe (c : SerialChain (n + 3)) (θ : Fin (n + 3) → ℝ) : RigidTransform :=
  (List.ofFn fun i : Fin n => Twist.exp (c.twist (Fin.castAdd 3 i)) (θ (Fin.castAdd 3 i))).prod

/-- **MLS p. 96: the wrist does not move the end-effector position.** For a chain with a spherical
wrist (`HasSphericalWrist`), the forward kinematics (3.3) is the arm's product of exponentials times
the pose with rotation `e^{ω̂₀θ₀} e^{ω̂₁θ₁} e^{ω̂₂θ₂} R_st(0)` and translation `p_st(0)`, where
`θᵢ` is the angle of wrist joint `n + i`. -/
theorem HasSphericalWrist.fk_eq {c : SerialChain (n + 3)} {ω : Fin 3 → Vec3}
    (hc : c.HasSphericalWrist ω) (θ : Fin (n + 3) → ℝ) :
    c.fk θ = c.armPoe θ *
      ⟨Rotation.exp (ω 0) (θ (Fin.natAdd n 0)) * Rotation.exp (ω 1) (θ (Fin.natAdd n 1)) *
        Rotation.exp (ω 2) (θ (Fin.natAdd n 2)) * c.toolRef.rotation, c.toolRef.translation⟩ := by
  have hsplit : c.poe θ = c.armPoe θ *
      (Twist.exp (c.twist (Fin.natAdd n 0)) (θ (Fin.natAdd n 0)) *
        (Twist.exp (c.twist (Fin.natAdd n 1)) (θ (Fin.natAdd n 1)) *
          Twist.exp (c.twist (Fin.natAdd n 2)) (θ (Fin.natAdd n 2)))) := by
    rw [poe, jointMotions, List.ofFn_add, List.prod_append]
    simp [armPoe, List.ofFn_succ, Fin.castAdd]
  rw [fk, hsplit, hc.twist_eq 0, hc.twist_eq 1, hc.twist_eq 2,
    Twist.exp_revolute _ _ (hc.norm_axis 0), Twist.exp_revolute _ _ (hc.norm_axis 1),
    Twist.exp_revolute _ _ (hc.norm_axis 2), mul_assoc]
  congr 1
  ext1
  · simp only [RigidTransform.mul_rotation, mul_assoc]
  · simp only [RigidTransform.mul_translation, RigidTransform.mul_rotation, Rotation.act_mul,
      map_sub, map_add]
    abel

/-- **MLS p. 96: `W_D = W_R` for a manipulator with a spherical wrist.** With the end-effector frame
at the wrist centre and an unrestricted joint space, the dextrous workspace (3.13) equals the
reachable workspace (3.12). -/
theorem HasSphericalWrist.dextrousWorkspace_eq {c : SerialChain (n + 3)} {ω : Fin 3 → Vec3}
    (hc : c.HasSphericalWrist ω) :
    c.dextrousWorkspace Set.univ = c.reachableWorkspace Set.univ := by
  refine Set.Subset.antisymm dextrousWorkspace_subset_reachableWorkspace ?_
  rintro p ⟨θ, -, rfl⟩ R
  obtain ⟨α, β, γ, hR⟩ := Rotation.exists_exp_mul_exp_mul_exp_eq (hc.norm_axis 0)
    (hc.norm_axis 1) (hc.norm_axis 2) hc.inner_zero_one hc.inner_one_two
    ((c.armPoe θ).rotation⁻¹ * R * c.toolRef.rotation⁻¹)
  let θ' : Fin (n + 3) → ℝ := Fin.append (fun i => θ (Fin.castAdd 3 i)) ![α, β, γ]
  have harm : c.armPoe θ' = c.armPoe θ := by
    simp [armPoe, θ']
  refine ⟨θ', Set.mem_univ _, ?_⟩
  have h0 : θ' (Fin.natAdd n 0) = α := by simp [θ']
  have h1 : θ' (Fin.natAdd n 1) = β := by simp [θ']
  have h2 : θ' (Fin.natAdd n 2) = γ := by simp [θ']
  beta_reduce
  rw [hc.fk_eq θ', hc.fk_eq θ, harm, h0, h1, h2, hR]
  ext1
  · simp only [RigidTransform.mul_rotation, mul_assoc, inv_mul_cancel, mul_one,
      mul_inv_cancel_left]
  · simp only [RigidTransform.mul_translation]

/-- **MLS p. 96: `W = W_R × SO(3)` for a manipulator with a spherical wrist.** With the end-effector
frame at the wrist centre and an unrestricted joint space, a pose `(p, R)` lies in the complete
workspace (3.11) exactly when its position `p` lies in the reachable workspace (3.12), whatever
the rotation `R`. -/
theorem HasSphericalWrist.completeWorkspace_eq {c : SerialChain (n + 3)} {ω : Fin 3 → Vec3}
    (hc : c.HasSphericalWrist ω) :
    c.completeWorkspace Set.univ = {g | g.translation ∈ c.reachableWorkspace Set.univ} := by
  ext g
  constructor
  · rintro ⟨θ, -, rfl⟩
    exact ⟨θ, Set.mem_univ _, rfl⟩
  · intro hg
    change g.translation ∈ c.reachableWorkspace Set.univ at hg
    rw [← hc.dextrousWorkspace_eq] at hg
    obtain ⟨θ, -, hθ⟩ := hg g.rotation
    exact ⟨θ, Set.mem_univ _, hθ⟩

end SerialChain
end RoboLean
