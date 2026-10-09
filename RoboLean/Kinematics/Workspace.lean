import RoboLean.Kinematics.SerialChain
import RoboLean.Geometry.RotationVelocity

/-!
# Manipulator workspaces

MLS Chapter 3, §2.4, printed p. 95, eqs. (3.11)–(3.13). For a serial chain with
product-of-exponentials forward kinematics `g_st : Q → SE(3)` (eq. (3.3), p. 87):

* the complete workspace `W = {g_st(θ) : θ ∈ Q} ⊂ SE(3)`, eq. (3.11);
* the reachable workspace `W_R = {p(θ) : θ ∈ Q} ⊂ ℝ³`, eq. (3.12), where `p(θ)` is the
  position component of `g_st(θ)`;
* the dextrous workspace `W_D = {p ∈ ℝ³ : ∀ R ∈ SO(3), ∃ θ with g_st(θ) = (p, R)}`,
  eq. (3.13), with the quantifier order exactly as printed.

Conventions. Joint coordinates are the real lift `Fin n → ℝ` of `SerialChain`, and the
configuration space `Q` of the book is passed as an explicit argument
`Q : Set (Fin n → ℝ)`; the chain's own admissible set is `c.admissible`, which one passes
as `Q` (MLS p. 84: `Q` may be a proper subset of joint space). A pose is a
`RigidTransform` with named fields `rotation` (in `SO(3)`) and `translation`; the
book's pair `(p, R)` is written `⟨R, p⟩`. These sets describe pose reachability of the
coordinate model only; they say nothing about path feasibility, dynamics or a physical
robot.
-/

noncomputable section

namespace RoboLean

namespace SerialChain

variable {n : ℕ}

/-- The complete workspace `W = {g_st(θ) : θ ∈ Q} ⊂ SE(3)` of MLS eq. (3.11), p. 95: the
image of the admissible joint set `Q` under the product-of-exponentials forward
kinematics (eq. (3.3), p. 87). Pass the chain's own domain as `Q := c.admissible`. This
is pose reachability only: it says nothing about the existence of a path between poses or
about dynamic feasibility. -/
def completeWorkspace (c : SerialChain n) (Q : Set (Fin n → ℝ)) : Set RigidTransform :=
  c.fk '' Q

/-- The reachable workspace `W_R = {p(θ) : θ ∈ Q} ⊂ ℝ³` of MLS eq. (3.12), p. 95, where
`p(θ)` is the translation (position) component of `g_st(θ)`. Pass the chain's own
domain as `Q := c.admissible`. A point belongs to it when it is reached at some
orientation; there is no quantifier over orientations. -/
def reachableWorkspace (c : SerialChain n) (Q : Set (Fin n → ℝ)) : Set Vec3 :=
  (fun θ => (c.fk θ).translation) '' Q

/-- The dextrous workspace
`W_D = {p ∈ ℝ³ : ∀ R ∈ SO(3), ∃ θ with g_st(θ) = (p, R)}` of MLS eq. (3.13), p. 95, with
the quantifier order as printed: for every rotation `R` there is a joint vector `θ`,
which may depend on `R`. The joint vector `θ` ranges over `Q`, the domain of the book's
`g_st : Q → SE(3)`; pass the chain's own domain as `Q := c.admissible`. The book's pair
`(p, R)` is the rigid transform `⟨R, p⟩`. -/
def dextrousWorkspace (c : SerialChain n) (Q : Set (Fin n → ℝ)) : Set Vec3 :=
  {p | ∀ R : Rotation, ∃ θ ∈ Q, c.fk θ = ⟨R, p⟩}

variable {c : SerialChain n} {Q Q' : Set (Fin n → ℝ)}

/-- The reachable workspace (MLS eq. (3.12), p. 95) is the translation image of the
complete workspace (eq. (3.11)): `p(θ)` is the position component of `g_st(θ)`. -/
theorem reachableWorkspace_eq_image :
    c.reachableWorkspace Q = RigidTransform.translation '' c.completeWorkspace Q := by
  rw [completeWorkspace, Set.image_image]
  rfl

/-- A point is in the dextrous workspace (MLS eq. (3.13), p. 95) exactly when every pose
with that position and an arbitrary rotation lies in the complete workspace
(eq. (3.11)). -/
theorem mem_dextrousWorkspace_iff {p : Vec3} :
    p ∈ c.dextrousWorkspace Q ↔
      ∀ R : Rotation, (⟨R, p⟩ : RigidTransform) ∈ c.completeWorkspace Q :=
  Iff.rfl

/-- Every point of the dextrous workspace (MLS eq. (3.13), p. 95) is in the reachable
workspace (eq. (3.12)): instantiate the orientation quantifier at the identity. -/
theorem dextrousWorkspace_subset_reachableWorkspace :
    c.dextrousWorkspace Q ⊆ c.reachableWorkspace Q := by
  intro p hp
  obtain ⟨θ, hθ, h⟩ := hp 1
  exact ⟨θ, hθ, by simp only [h]⟩

/-- Shrinking the admissible joint set (MLS p. 84, e.g. by joint limits) shrinks the
complete workspace of MLS eq. (3.11), p. 95. -/
theorem completeWorkspace_mono (h : Q ⊆ Q') :
    c.completeWorkspace Q ⊆ c.completeWorkspace Q' :=
  Set.image_mono h

/-- Shrinking the admissible joint set (MLS p. 84) shrinks the reachable workspace of
MLS eq. (3.12), p. 95. -/
theorem reachableWorkspace_mono (h : Q ⊆ Q') :
    c.reachableWorkspace Q ⊆ c.reachableWorkspace Q' :=
  Set.image_mono h

/-- Shrinking the admissible joint set (MLS p. 84) shrinks the dextrous workspace of
MLS eq. (3.13), p. 95. -/
theorem dextrousWorkspace_mono (h : Q ⊆ Q') :
    c.dextrousWorkspace Q ⊆ c.dextrousWorkspace Q' := by
  intro p hp R
  obtain ⟨θ, hθ, hR⟩ := hp R
  exact ⟨θ, h hθ, hR⟩

/-- When the reference configuration `θ = 0` is admissible, the reference tool pose
`g_st(0)` (MLS p. 87) lies in the complete workspace (MLS eq. (3.11), p. 95). -/
theorem toolRef_mem_completeWorkspace (h : (0 : Fin n → ℝ) ∈ Q) :
    c.toolRef ∈ c.completeWorkspace Q :=
  ⟨0, h, c.fk_zero⟩

/-- When the reference configuration `θ = 0` is admissible, the position of the
reference tool pose `g_st(0)` (MLS p. 87) lies in the reachable workspace
(MLS eq. (3.12), p. 95). -/
theorem toolRef_translation_mem_reachableWorkspace (h : (0 : Fin n → ℝ) ∈ Q) :
    c.toolRef.translation ∈ c.reachableWorkspace Q :=
  ⟨0, h, by simp only [c.fk_zero]⟩

/-- With no joints, the forward kinematics (MLS eq. (3.3), p. 87) is the constant
reference tool pose. -/
private theorem fk_of_zero_joints (c : SerialChain 0) (θ : Fin 0 → ℝ) :
    c.fk θ = c.toolRef := by
  rw [Subsingleton.elim θ 0, c.fk_zero]

/-- A chain with zero joints reaches exactly the position of its fixed tool pose: its
reachable workspace (MLS eq. (3.12), p. 95) over all of joint space is the singleton
`{p_st(0)}` (MLS p. 87). With `dextrousWorkspace_of_zero_joints` this is a satisfiable
instance in which the reachable and dextrous workspaces differ. -/
theorem reachableWorkspace_of_zero_joints (c : SerialChain 0) :
    c.reachableWorkspace Set.univ = {c.toolRef.translation} := by
  ext p
  simp [reachableWorkspace, fk_of_zero_joints]

/-- A chain with zero joints has an empty dextrous workspace (MLS eq. (3.13), p. 95): its
single pose cannot have both the identity rotation and the rotation by `π` about the
z-axis (`Rotation.zRotation`, MLS p. 31). Together with
`reachableWorkspace_of_zero_joints` this shows that the quantifier `∀ R ∃ θ` of
eq. (3.13) is not implied by reachability. -/
theorem dextrousWorkspace_of_zero_joints (c : SerialChain 0) :
    c.dextrousWorkspace Set.univ = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  obtain ⟨θ₁, -, h₁⟩ := hp 1
  obtain ⟨θ₂, -, h₂⟩ := hp (Rotation.zRotation Real.pi)
  rw [fk_of_zero_joints] at h₁ h₂
  have hR : (1 : Rotation) = Rotation.zRotation Real.pi :=
    (congrArg RigidTransform.rotation h₁).symm.trans (congrArg RigidTransform.rotation h₂)
  have h00 := congrArg (fun R : Rotation => R.val 0 0) hR
  simp only [Rotation.zRotation_val] at h00
  norm_num at h00

end SerialChain

end RoboLean
