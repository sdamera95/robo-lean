import RoboLean.Geometry.TwistExpAdjoint
import RoboLean.Geometry.TwistScrewMotion
import RoboLean.Geometry.ScrewConjugation
import RoboLean.Geometry.RotationParameters

/-!
# Serial chains and product-of-exponentials forward kinematics

MLS Chapter 3, §2, printed pp. 83–89. An open chain has `n` joints numbered from the
base (p. 83). Lean joint `i : Fin n` is the book's joint `i + 1`; links are indexed by
`Fin (n + 1)`, link `0` is the base, and Lean joint `i` connects link `i`
(`Fin.castSucc i`) to link `i + 1` (`Fin.succ i`).

Joint coordinates are real numbers, `θ : Fin n → ℝ`. The book's revolute coordinate
lives on the circle `S¹` (p. 84); here it is a real lift, and periodicity is the
theorem `SerialChain.fk_add_int_mul_two_pi`, not a quotient type. An admissible
subset of joint space is an explicit set (p. 84).

Reference joint twists are base-frame twists at the reference configuration `θ = 0`
(p. 87), in the library order `(v, ω)`. The forward kinematics map is the ordered,
noncommutative product `exp(ξ₁θ₁) ⋯ exp(ξₙθₙ) g_st(0)` of eq. (3.3), with the right
factor acting first, as in `geometry-conventions.md`.

Two semantics are defined without the product formula and proved equal to it (ledger
K05): sequential joint motion about the current joint axes (pp. 86–87,
`SerialChain.toolPose_runMoves_perm`) and adjacent link-frame composition (eq. (3.1),
p. 85, `LinkFrameChain.fk_eq_toSerialChain_fk`). These are statements about the
coordinate model; they assert nothing about a physical robot's calibration.
-/

noncomputable section

namespace RoboLean

namespace Twist

/-- The twist of a revolute joint with axis direction `ω` through the point `q`,
`ξ = (-ω × q, ω)` in the order `(v, ω)`: MLS p. 87 (Chapter 3, §2.2). The book takes
`ω` to be a unit vector; the definition is algebraic, and the unit premise is carried by
`Twist.IsRevoluteJoint`. -/
def revolute (ω q : Vec3) : Twist := ⟨-Vec3.cross ω q, ω⟩

/-- The revolute joint twist of MLS p. 87 is the zero-pitch case of the screw generator
`Twist.fromScrew` (MLS p. 47, the screw generator `v = −ω × q + hω` in the text after
eq. (2.40), with `h = 0`; Proposition 2.10, p. 48). -/
theorem revolute_eq_fromScrew (ω q : Vec3) : revolute ω q = fromScrew ω q 0 := by
  simp [revolute, fromScrew]

/-- MLS p. 87 lets `q` be "any point on the axis": every point of the line through `q`
with direction `ω` gives the same revolute twist. -/
theorem revolute_axis_point (ω q q' : Vec3) (hq : q' ∈ axisLine q ω) :
    revolute ω q' = revolute ω q := by
  obtain ⟨r, rfl⟩ := (mem_axisLine_iff q ω q').mp hq
  rw [revolute_eq_fromScrew, revolute_eq_fromScrew, fromScrew_axis_shift]

/-- The revolute joint twist `(-ω × q, ω)` of MLS p. 87 is linear in the axis direction `ω`
for a fixed axis point `q`. Supporting lemma for Example 3.13, p. 126. -/
def revoluteLinear (q : Vec3) : Vec3 →ₗ[ℝ] Twist where
  toFun ω := revolute ω q
  map_add' ω η := by
    apply Twist.ext
    · simp [revolute, add_comm]
    · rfl
  map_smul' c ω := by
    apply Twist.ext
    · simp [revolute]
    · rfl

/-- `revoluteLinear q ω` is the revolute twist `Twist.revolute ω q` of MLS p. 87. -/
@[simp] theorem revoluteLinear_apply (q ω : Vec3) : revoluteLinear q ω = revolute ω q := rfl

/-- The revolute twist depends on the axis point only through `ω × q`: if
`ω × (q₁ - q₂) = 0`, both points give the same twist. This is condition 2 of MLS
Example 3.11, p. 124, and the condition of Example 3.13, p. 126. -/
theorem revolute_eq_of_cross_sub_eq_zero (ω q₁ q₂ : Vec3)
    (h : Vec3.cross ω (q₁ - q₂) = 0) : revolute ω q₁ = revolute ω q₂ := by
  have h' : Vec3.cross ω q₁ = Vec3.cross ω q₂ := by
    have hs : Vec3.cross ω (q₁ - q₂) = Vec3.cross ω q₁ - Vec3.cross ω q₂ := by
      rw [sub_eq_add_neg, Vec3.cross_add, Vec3.cross_neg, ← sub_eq_add_neg]
    rw [hs] at h
    exact sub_eq_zero.mp h
  apply Twist.ext
  · simp [revolute, h']
  · rfl

/-- Two revolute twists with parallel axes `ω₂ = ±ω₁` and collinear axis lines
(`ω₁ × (q₁ - q₂) = 0`) are proportional, `ξ₂ = ±ξ₁`: the column computation in the proof of
MLS Example 3.11, p. 124–125. The unit-magnitude premise of the book is not needed. -/
theorem revolute_eq_smul_of_collinear (ω₁ ω₂ q₁ q₂ : Vec3) (s : ℝ) (hω : ω₂ = s • ω₁)
    (hcol : Vec3.cross ω₁ (q₁ - q₂) = 0) : revolute ω₂ q₂ = s • revolute ω₁ q₁ := by
  rw [revolute_eq_of_cross_sub_eq_zero ω₁ q₁ q₂ hcol, hω]
  apply Twist.ext
  · simp [revolute]
  · rfl

/-- The twist `(v, 0)` of a prismatic joint translating along `v`: MLS p. 87. The book
takes `v` to be a unit vector; the unit premise is carried by
`Twist.IsPrismaticJoint`. -/
def prismatic (v : Vec3) : Twist := ⟨v, 0⟩

/-- A twist is a revolute joint twist when it has the form `(-ω × q, ω)` of MLS p. 87
with a unit axis direction `ω`. -/
def IsRevoluteJoint (ξ : Twist) : Prop :=
  ∃ ω q : Vec3, ‖ω‖ = 1 ∧ ξ = revolute ω q

/-- A twist is a prismatic joint twist when it has the form `(v, 0)` of MLS p. 87 with a
unit direction `v`. -/
def IsPrismaticJoint (ξ : Twist) : Prop :=
  ∃ v : Vec3, ‖v‖ = 1 ∧ ξ = prismatic v

/-- The motion generated by a revolute twist with unit axis: rotation `R = exp(θ ω̂)` and
translation `q - R q`, the zero-pitch case of MLS eq. (2.40), p. 47; this is the joint
motion "rotating about the axis" of MLS p. 85. All real angles are allowed. -/
theorem exp_revolute (ω q : Vec3) (hω : ‖ω‖ = 1) (t : ℝ) :
    exp (revolute ω q) t = ⟨Rotation.exp ω t, q - (Rotation.exp ω t).act q⟩ := by
  rw [revolute_eq_fromScrew, exp_fromScrew ω q 0 t hω]
  simp

/-- A revolute joint motion rotates every point about the joint axis:
`x ↦ R (x - q) + q` (MLS p. 47, eq. (2.40) with zero pitch; MLS p. 85). -/
theorem exp_revolute_applyPoint (ω q : Vec3) (hω : ‖ω‖ = 1) (t : ℝ) (x : Vec3) :
    (exp (revolute ω q) t).applyPoint x = (Rotation.exp ω t).act (x - q) + q := by
  rw [revolute_eq_fromScrew, exp_fromScrew_applyPoint ω q 0 t hω]
  simp

/-- A revolute joint motion fixes every point of its axis: if `x` lies on the line through `q`
with unit direction `ω`, then `exp(ξ̂t) x = x` for `ξ = (-ω × q, ω)`. This is the fact
"`exp(ξ̂θ)p = p` if `p` is on the axis of a revolute twist `ξ`" of MLS p. 104, used to
eliminate joint angles in inverse kinematics (§3.3). -/
theorem exp_revolute_applyPoint_of_mem_axisLine (ω q : Vec3) (hω : ‖ω‖ = 1) (t : ℝ)
    {x : Vec3} (hx : x ∈ axisLine q ω) : (exp (revolute ω q) t).applyPoint x = x := by
  obtain ⟨r, rfl⟩ := (mem_axisLine_iff q ω x).mp hx
  rw [exp_revolute_applyPoint ω q hω, add_sub_cancel_left, map_smul,
    Rotation.exp_act_unit_axis ω hω, add_comm]

/-- The motion generated by a prismatic twist is the translation by `t v`
(MLS p. 85: "θ ∈ ℝ is the amount of translation"; eq. (2.41), p. 47). -/
theorem exp_prismatic (v : Vec3) (t : ℝ) :
    exp (prismatic v) t = (⟨1, t • v⟩ : RigidTransform) :=
  exp_pure_translation v t

/-- Revolute joint motions are `2π`-periodic in the joint angle (MLS p. 84: the angle
`2π` is equated to the angle `0`), for every integer number of turns. -/
theorem IsRevoluteJoint.exp_add_int_mul_two_pi {ξ : Twist} (hξ : ξ.IsRevoluteJoint)
    (θ : ℝ) (k : ℤ) : exp ξ (θ + k * (2 * Real.pi)) = exp ξ θ := by
  obtain ⟨ω, q, hω, rfl⟩ := hξ
  rw [exp_revolute ω q hω, exp_revolute ω q hω, Rotation.exp_add_int_mul_two_pi ω hω]

/-- The adjoint of a rigid transform moves a revolute twist to the revolute twist of the
moved axis, with direction `g_* ω` and point `g q`. This is the "ith joint twist,
transformed to the current manipulator configuration" of MLS p. 116; the adjoint is
MLS eq. (2.58), p. 55. -/
theorem adjoint_revolute (g : RigidTransform) (ω q : Vec3) :
    adjoint g (revolute ω q) = revolute (g.applyVector ω) (g.applyPoint q) := by
  rw [revolute_eq_fromScrew, revolute_eq_fromScrew, adjoint_fromScrew]

/-- The adjoint (MLS eq. (2.58), p. 55) moves a prismatic twist to the prismatic twist
along the rotated direction `g_* v`; translation of the frame does not enter. -/
theorem adjoint_prismatic (g : RigidTransform) (v : Vec3) :
    adjoint g (prismatic v) = prismatic (g.applyVector v) := by
  apply Twist.ext
  · simp [adjoint, prismatic, RigidTransform.applyVector]
  · simp [adjoint, prismatic]

/-- Transporting a revolute joint twist by a rigid transform gives a revolute joint
twist (unit axis preserved); supports MLS p. 116 and eq. (2.58). -/
theorem IsRevoluteJoint.adjoint {ξ : Twist} (hξ : ξ.IsRevoluteJoint) (g : RigidTransform) :
    (Twist.adjoint g ξ).IsRevoluteJoint := by
  obtain ⟨ω, q, hω, rfl⟩ := hξ
  exact ⟨g.applyVector ω, g.applyPoint q, by simpa using hω, adjoint_revolute g ω q⟩

/-- Transporting a prismatic joint twist by a rigid transform gives a prismatic joint
twist (unit direction preserved); supports MLS p. 116 and eq. (2.58). -/
theorem IsPrismaticJoint.adjoint {ξ : Twist} (hξ : ξ.IsPrismaticJoint) (g : RigidTransform) :
    (Twist.adjoint g ξ).IsPrismaticJoint := by
  obtain ⟨v, hv, rfl⟩ := hξ
  exact ⟨g.applyVector v, by simpa using hv, adjoint_prismatic g v⟩

end Twist

/-- An open serial chain with `n` joints, numbered from the base (MLS p. 83).

* `twist i` is the reference twist `ξ_{i+1}` of Lean joint `i`, written in the base frame
  `S` at the reference configuration `θ = 0` (MLS p. 87). The structure does not force a
  revolute or prismatic form (MLS p. 83 restricts to those two joint types); results
  that need a joint type take `Twist.IsRevoluteJoint` or `Twist.IsPrismaticJoint` as an
  explicit hypothesis.
* `toolRef` is `g_st(0)`, the tool frame relative to the base frame in the reference
  configuration (MLS p. 87).
* `admissible` is the joint space `Q` as an explicit subset of the real lift
  `Fin n → ℝ` (MLS p. 84: `Q` may be a subset of the unrestricted joint space); it
  defaults to all of `Fin n → ℝ`. Revolute coordinates are real numbers, not points of
  `S¹`; see `SerialChain.fk_add_int_mul_two_pi`. It is read by the workspaces over the
  chain's own joint space (`SerialChain.admissibleCompleteWorkspace` and its reachable and
  dextrous variants) and by the closed-chain joint space `ClosedChain.admissible`; the
  workspace definitions with an explicit `Q` and the forward kinematics do not read it. -/
structure SerialChain (n : ℕ) where
  /-- Reference base-frame joint twists, base to tip (MLS p. 87). -/
  twist : Fin n → Twist
  /-- The reference tool pose `g_st(0)` (MLS p. 87). -/
  toolRef : RigidTransform
  /-- The admissible joint coordinates `Q` (MLS p. 84). -/
  admissible : Set (Fin n → ℝ) := Set.univ

namespace SerialChain

variable {n : ℕ}

/-- The ordered list `[exp(ξ₁θ₁), …, exp(ξₙθₙ)]` of joint motions, base first, as in the
product of exponentials formula, MLS eq. (3.3), p. 87. -/
def jointMotions (c : SerialChain n) (θ : Fin n → ℝ) : List RigidTransform :=
  List.ofFn fun i => Twist.exp (c.twist i) (θ i)

/-- The ordered product `exp(ξ₁θ₁) ⋯ exp(ξₙθₙ)` of MLS eq. (3.3), p. 87, as a list
product in the noncommutative group of rigid transforms; the right factor acts first. -/
def poe (c : SerialChain n) (θ : Fin n → ℝ) : RigidTransform :=
  (c.jointMotions θ).prod

/-- Product-of-exponentials forward kinematics, MLS eq. (3.3), p. 87:
`g_st(θ) = exp(ξ₁θ₁) ⋯ exp(ξₙθₙ) g_st(0)`. It is defined for every real joint vector;
restriction to the admissible set is explicit where needed. -/
def fk (c : SerialChain n) (θ : Fin n → ℝ) : RigidTransform :=
  c.poe θ * c.toolRef

/-- At the reference configuration every joint motion is the identity (MLS p. 87). -/
@[simp] theorem poe_zero (c : SerialChain n) : c.poe 0 = 1 := by
  apply List.prod_eq_one
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  simp

/-- `g_st(0)` is the tool pose of the reference configuration `θ = 0` (MLS p. 87). -/
@[simp] theorem fk_zero (c : SerialChain n) : c.fk 0 = c.toolRef := by
  simp [fk]

/-- MLS eq. (3.30), p. 105: post-multiplying `g_st(θ) = g_d` by `g_st(0)⁻¹` isolates the
product of exponentials, `exp(ξ̂₁θ₁) ⋯ exp(ξ̂ₙθₙ) = g_d g_st(0)⁻¹`. Holds for every chain and
every real joint vector. -/
theorem fk_eq_iff_poe_eq (c : SerialChain n) (θ : Fin n → ℝ) (g : RigidTransform) :
    c.fk θ = g ↔ c.poe θ = g * c.toolRef⁻¹ := by
  rw [fk, eq_mul_inv_iff_mul_eq]

/-- The chain of the joints after the base joint, with the same base frame and the same
reference tool pose. Its forward kinematics is the motion of the tool when the base joint
is held at zero (MLS p. 86); its admissible set is the unrestricted default. -/
def tail (c : SerialChain (n + 1)) : SerialChain n where
  twist := Fin.tail c.twist
  toolRef := c.toolRef

/-- The base joint motion is the first factor of the product of exponentials
(MLS eq. (3.3), p. 87). -/
theorem jointMotions_succ (c : SerialChain (n + 1)) (θ : Fin (n + 1) → ℝ) :
    c.jointMotions θ =
      Twist.exp (c.twist 0) (θ 0) :: c.tail.jointMotions (Fin.tail θ) :=
  List.ofFn_succ

/-- The forward kinematics factors as the base joint motion applied to the forward
kinematics of the remaining joints (MLS eq. (3.2), p. 86, generalized by eq. (3.3)). -/
theorem fk_succ (c : SerialChain (n + 1)) (θ : Fin (n + 1) → ℝ) :
    c.fk θ = Twist.exp (c.twist 0) (θ 0) * c.tail.fk (Fin.tail θ) := by
  simp only [fk, poe, jointMotions_succ, List.prod_cons, mul_assoc]
  rfl

/-- MLS p. 84, revolute coordinates: the forward kinematics is unchanged when any
revolute joint coordinates are shifted by integer multiples of `2π`. Only coordinates
with `k i ≠ 0` must belong to revolute joints (unit axis, MLS p. 87); prismatic and other
coordinates are left unshifted. This is the explicit bridge from the real lift to the
book's `S¹` coordinates (ledger K01). -/
theorem fk_add_int_mul_two_pi (c : SerialChain n) (θ : Fin n → ℝ) (k : Fin n → ℤ)
    (hk : ∀ i, k i ≠ 0 → (c.twist i).IsRevoluteJoint) :
    c.fk (fun i => θ i + k i * (2 * Real.pi)) = c.fk θ := by
  have hf : (fun i => Twist.exp (c.twist i) (θ i + k i * (2 * Real.pi))) =
      fun i => Twist.exp (c.twist i) (θ i) := by
    funext i
    by_cases h : k i = 0
    · simp [h]
    · exact (hk i h).exp_add_int_mul_two_pi (θ i) (k i)
  simp only [fk, poe, jointMotions, hf]

/-- One revolute coordinate shifted by `2π` leaves the forward kinematics unchanged
(MLS p. 84; special case of `fk_add_int_mul_two_pi`). -/
theorem fk_update_add_two_pi (c : SerialChain n) (θ : Fin n → ℝ) (i : Fin n)
    (hi : (c.twist i).IsRevoluteJoint) :
    c.fk (Function.update θ i (θ i + 2 * Real.pi)) = c.fk θ := by
  classical
  have h := c.fk_add_int_mul_two_pi θ (Pi.single i 1) (by
    intro j hj
    by_cases hji : j = i
    · exact hji ▸ hi
    · simp [hji] at hj)
  convert h using 2
  funext j
  by_cases hji : j = i
  · subst hji
    simp
  · simp [hji]

/-! ### Sequential joint motion (MLS pp. 86–87)

A state assigns to every link `j : Fin (n + 1)` its active rigid displacement from the
reference configuration, in base coordinates. Moving one joint moves the links distal to
it about the joint's current axis, which is carried by the proximal link. These
definitions do not use the product formula. -/

/-- The reference state: no link has moved (MLS p. 87, reference configuration). -/
def referenceState : Fin (n + 1) → RigidTransform := fun _ => 1

/-- Move Lean joint `i` (connecting link `i` to link `i + 1`) by `t`, holding all other
joints, as in MLS pp. 86–87. Links `j ≤ i` stay. Every link `j > i` is displaced by the
screw motion `exp(ξ'ᵢ t)` about the joint's current axis `ξ'ᵢ = Ad_{G i} ξᵢ`, where
`G i` is the current displacement of the proximal link that carries the axis
(MLS p. 86: "this motion moves the axis of θ₂ … ξ₂' = Ad ξ₂"). -/
def moveJoint (c : SerialChain n) (i : Fin n) (t : ℝ) (G : Fin (n + 1) → RigidTransform) :
    Fin (n + 1) → RigidTransform :=
  fun j => if i.castSucc < j then
    Twist.exp (Twist.adjoint (G i.castSucc) (c.twist i)) t * G j else G j

/-- Perform a list of single-joint moves `(joint, displacement)` in order, each by
`moveJoint` (MLS pp. 86–87: joints may be moved one at a time in any order). -/
def runMoves (c : SerialChain n) (ms : List (Fin n × ℝ)) (G : Fin (n + 1) → RigidTransform) :
    Fin (n + 1) → RigidTransform :=
  ms.foldl (fun G m => c.moveJoint m.1 m.2 G) G

/-- The joint coordinates accumulated by a list of moves: the sum, per joint, of the
commanded displacements (supports MLS pp. 86–87). -/
def jointTotals (ms : List (Fin n × ℝ)) : Fin n → ℝ :=
  (ms.map fun m => Pi.single m.1 m.2).sum

/-- The tool pose of a state: the tool frame is rigid with the last link, so its pose is
the last link's displacement applied to `g_st(0)` by left multiplication (MLS p. 85,
`g_ab(θ) = exp(ξ̂θ) g_ab(0)`; active displacement as in MLS eq. (2.37), p. 42). -/
def toolPose (c : SerialChain n) (G : Fin (n + 1) → RigidTransform) : RigidTransform :=
  G (Fin.last n) * c.toolRef

/-- The link displacements predicted by the product of exponentials: link `j` is moved by
the product of the first `j` joint exponentials (MLS p. 116: "the rigid body
transformation which takes the ith joint frame from its reference configuration to the
current configuration"). -/
def linkPOE (c : SerialChain n) (θ : Fin n → ℝ) : Fin (n + 1) → RigidTransform :=
  fun j => ((c.jointMotions θ).take j).prod

/-- The predicted link displacements vanish at the reference configuration (MLS p. 87). -/
@[simp] theorem linkPOE_zero (c : SerialChain n) : c.linkPOE 0 = referenceState := by
  funext j
  apply List.prod_eq_one
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hx)
  simp

/-- The predicted last-link displacement gives the product-of-exponentials tool pose,
MLS eq. (3.3), p. 87. -/
@[simp] theorem toolPose_linkPOE (c : SerialChain n) (θ : Fin n → ℝ) :
    c.toolPose (c.linkPOE θ) = c.fk θ := by
  simp only [toolPose, linkPOE, fk, poe, Fin.val_last]
  rw [List.take_of_length_le (by simp [jointMotions])]

private theorem ofFn_update {α : Type*} (f : Fin n → α) (i : Fin n) (a : α) :
    List.ofFn (Function.update f i a) = (List.ofFn f).set i a := by
  apply List.ext_getElem (by simp)
  intro k h₁ h₂
  rw [List.getElem_ofFn, List.getElem_set, List.getElem_ofFn, Function.update_apply]
  by_cases hk : (i : ℕ) = k
  · simp only [hk, ite_true]
    have : (⟨k, by simpa using h₁⟩ : Fin n) = i := Fin.ext hk.symm
    simp [this]
  · simp only [hk, ite_false]
    have : (⟨k, by simpa using h₁⟩ : Fin n) ≠ i := fun h => hk (by rw [← h])
    simp [this]

private theorem jointMotions_add_single (c : SerialChain n) (θ : Fin n → ℝ) (i : Fin n)
    (t : ℝ) :
    c.jointMotions (θ + Pi.single i t) =
      (c.jointMotions θ).set i (Twist.exp (c.twist i) (θ i + t)) := by
  classical
  rw [jointMotions, jointMotions, ← ofFn_update]
  congr 1
  funext k
  by_cases hk : k = i
  · subst hk
    simp
  · simp [hk]

/-- **Sequential-motion invariant (MLS pp. 86–87).** Moving joint `i` by `t` from the
link displacements predicted by the product of exponentials at `θ` gives the
displacements predicted at `θ + t eᵢ`. The move itself is defined by the screw motion
about the current axis (`moveJoint`), not by the product formula. -/
theorem moveJoint_linkPOE (c : SerialChain n) (θ : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    c.moveJoint i t (c.linkPOE θ) = c.linkPOE (θ + Pi.single i t) := by
  funext j
  simp only [moveJoint, linkPOE, Fin.val_castSucc]
  rw [jointMotions_add_single]
  set l := c.jointMotions θ
  have hlen : l.length = n := by simp [l, jointMotions]
  split_ifs with hij
  · rw [Fin.lt_def, Fin.val_castSucc] at hij
    have hi : (i : ℕ) < (l.take j).length := by
      rw [List.length_take, hlen]
      exact lt_min hij i.isLt
    have hP : (l.take i) = (l.take j).take i := by
      rw [List.take_take, min_eq_left hij.le]
    have hE : (l.take j)[(i : ℕ)] = Twist.exp (c.twist i) (θ i) := by
      simp [l, jointMotions]
    have hself : (l.take j).set i (Twist.exp (c.twist i) (θ i)) = l.take j := by
      rw [← hE]
      exact List.set_getElem_self hi
    have hsplit := List.prod_set (l.take j) i (Twist.exp (c.twist i) (θ i))
    simp only [hself, hi, ite_true] at hsplit
    rw [List.take_set, List.prod_set]
    simp only [hi, ite_true]
    rw [hsplit, Twist.exp_adjoint, ← hP, add_comm (θ i) t, Twist.exp_add]
    group
  · rw [Fin.lt_def, Fin.val_castSucc, not_lt] at hij
    rw [List.take_set_of_le hij]

/-- Running moves from the predicted state at `θ` gives the predicted state at `θ` plus
the accumulated joint displacements (MLS pp. 86–87). -/
theorem runMoves_linkPOE (c : SerialChain n) (ms : List (Fin n × ℝ)) (θ : Fin n → ℝ) :
    c.runMoves ms (c.linkPOE θ) = c.linkPOE (θ + jointTotals ms) := by
  induction ms generalizing θ with
  | nil => simp [runMoves, jointTotals]
  | cons m ms ih =>
    simp only [runMoves, List.foldl_cons] at ih ⊢
    rw [moveJoint_linkPOE, ih]
    simp [jointTotals, add_assoc]

/-- **K05, sequential-motion form (MLS pp. 86–87, eq. (3.3)).** Starting from the
reference configuration and moving the joints one at a time, in any order and any number
of times, each move being the screw motion about that joint's current axis, the tool
reaches the product-of-exponentials pose at the accumulated joint coordinates. -/
theorem toolPose_runMoves (c : SerialChain n) (ms : List (Fin n × ℝ)) :
    c.toolPose (c.runMoves ms referenceState) = c.fk (jointTotals ms) := by
  have h := c.runMoves_linkPOE ms 0
  rw [linkPOE_zero, zero_add] at h
  rw [h, toolPose_linkPOE]

/-- Moving each joint exactly once, by `θᵢ`, in any order accumulates the joint vector
`θ` (supports MLS p. 87: the result does not depend on the order of the motions). -/
theorem jointTotals_of_perm {θ : Fin n → ℝ} {ms : List (Fin n × ℝ)}
    (hms : ms.Perm (List.ofFn fun i => (i, θ i))) : jointTotals ms = θ := by
  classical
  rw [jointTotals, (hms.map _).sum_eq, List.map_ofFn, List.sum_ofFn]
  exact Finset.univ_sum_single θ

/-- **K05, order independence (MLS p. 87).** Moving every joint `i` once by `θᵢ`, in any
order (any permutation of the moves), each about its current axis, brings the tool to
`g_st(θ) = exp(ξ₁θ₁) ⋯ exp(ξₙθₙ) g_st(0)` of eq. (3.3). The book's two-joint
derivations on p. 86 (θ₂ first, or θ₁ first) are the two orders for `n = 2`. -/
theorem toolPose_runMoves_perm (c : SerialChain n) {θ : Fin n → ℝ}
    {ms : List (Fin n × ℝ)} (hms : ms.Perm (List.ofFn fun i => (i, θ i))) :
    c.toolPose (c.runMoves ms referenceState) = c.fk θ := by
  rw [toolPose_runMoves, jointTotals_of_perm hms]

/-- MLS p. 87: the reference twist `ξᵢ` is the screw motion of joint `i` "with all other
joint angles held fixed at θⱼ = 0": moving joint `i` alone by `t` from the reference
configuration carries the tool by `exp(ξᵢ t)`. Proved from the sequential-motion
semantics. -/
theorem fk_single (c : SerialChain n) (i : Fin n) (t : ℝ) :
    c.fk (Pi.single i t) = Twist.exp (c.twist i) t * c.toolRef := by
  have h := c.toolPose_runMoves [(i, t)]
  simp only [jointTotals, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero] at h
  rw [← h]
  simp [runMoves, moveJoint, toolPose, referenceState, Fin.castSucc_lt_last]

end SerialChain

/-! ### Adjacent link frames (MLS eq. (3.1), p. 85; MLS p. 94, eqs. (3.7), (3.8), (3.10)) -/

/-- An open chain described by adjacent link frames, MLS p. 85 and eq. (3.1). Lean joint
`i` connects link frame `Lᵢ` to `Lᵢ₊₁`, with `L₀ = S` the base frame. MLS p. 94,
eqs. (3.7), (3.8), (3.10): the relative transform of adjacent frames is
`exp(ζ̂θ) g(0)` (3.7), the forward kinematics is their chained product (3.8), and the
base-frame joint twists follow from the adjacent-frame twists by an adjoint (3.10).

* `jointTwist i` is the joint twist `ζᵢ` written in the proximal link frame `Lᵢ`, where
  the joint axis is fixed.
* `linkRef i` is the reference relative transform `g_{Lᵢ Lᵢ₊₁}(0)`.
* `toolOffset` is the fixed transform `g_{Lₙ T}` from the tool frame to the last link
  frame. -/
structure LinkFrameChain (n : ℕ) where
  /-- Joint twists, each in the frame of the link that carries the joint axis. -/
  jointTwist : Fin n → Twist
  /-- Reference transforms between adjacent link frames, `g_{Lᵢ Lᵢ₊₁}(0)`. -/
  linkRef : Fin n → RigidTransform
  /-- The tool offset `g_{Lₙ T}` (MLS eq. (3.1)). -/
  toolOffset : RigidTransform

namespace LinkFrameChain

variable {n : ℕ}

/-- The transform between adjacent link frames, `g_{Lᵢ Lᵢ₊₁}(θᵢ) = exp(ζ̂ᵢ θᵢ) g_{Lᵢ Lᵢ₊₁}(0)`:
the joint motion about an axis fixed in `Lᵢ` acting on the reference relative pose
(MLS p. 85, `g_ab(θ) = exp(ξ̂θ) g_ab(0)`). -/
def relative (c : LinkFrameChain n) (i : Fin n) (t : ℝ) : RigidTransform :=
  Twist.exp (c.jointTwist i) t * c.linkRef i

/-- Forward kinematics by composing adjacent link frames, MLS eq. (3.1), p. 85:
`g_st(θ) = g_{s l₁}(θ₁) g_{l₁ l₂}(θ₂) ⋯ g_{lₙ₋₁ lₙ}(θₙ) g_{lₙ t}`. -/
def fk (c : LinkFrameChain n) (θ : Fin n → ℝ) : RigidTransform :=
  (List.ofFn fun i => c.relative i (θ i)).prod * c.toolOffset

/-- The reference pose `g_{S Lₖ}(0)` of link frame `k`, the product of the first `k`
reference relative transforms (MLS eq. (3.1) at `θ = 0`). -/
def refLinkPose (c : LinkFrameChain n) (k : ℕ) : RigidTransform :=
  ((List.ofFn c.linkRef).take k).prod

/-- The base-frame serial chain of an adjacent-frame description: the joint twist of joint
`i` moved to the base frame, `ξᵢ = Ad_{g_{S Lᵢ}(0)} ζᵢ` (MLS eq. (2.58), p. 55, and
p. 87, "all vectors and points are specified relative to the base coordinate frame"),
and `g_st(0) = g_{S Lₙ}(0) g_{Lₙ T}`. This is MLS p. 94, eqs. (3.7), (3.8), (3.10), where
(3.10) is `ξᵢ = Ad_{g_{l₀ lᵢ₋₁}(0)} ξ_{i−1,i}`; Lean joint `i` is the book's joint `i + 1`
and Lean `Lᵢ` is the book's `lᵢ`. -/
def toSerialChain (c : LinkFrameChain n) : SerialChain n where
  twist i := Twist.adjoint (c.refLinkPose i) (c.jointTwist i)
  toolRef := (List.ofFn c.linkRef).prod * c.toolOffset

/-- The adjacent-frame chain without its first joint, with link frame `L₁` as its base
frame: the last `n` factors of MLS eq. (3.1), p. 85. -/
def tail (c : LinkFrameChain (n + 1)) : LinkFrameChain n where
  jointTwist := Fin.tail c.jointTwist
  linkRef := Fin.tail c.linkRef
  toolOffset := c.toolOffset

private theorem refLinkPose_succ (c : LinkFrameChain (n + 1)) (k : ℕ) :
    c.refLinkPose (k + 1) = c.linkRef 0 * c.tail.refLinkPose k := by
  simp only [refLinkPose, List.ofFn_succ, List.take_succ_cons, List.prod_cons]
  rfl

private theorem twistedMotions_succ (c : LinkFrameChain (n + 1)) (θ : Fin (n + 1) → ℝ)
    (P : RigidTransform) :
    (List.ofFn fun i =>
        Twist.exp (Twist.adjoint (P * c.refLinkPose i) (c.jointTwist i)) (θ i)) =
      Twist.exp (Twist.adjoint P (c.jointTwist 0)) (θ 0) ::
        List.ofFn fun i => Twist.exp (Twist.adjoint (P * c.linkRef 0 * c.tail.refLinkPose i)
          (c.tail.jointTwist i)) (Fin.tail θ i) := by
  rw [List.ofFn_succ]
  congr 1
  · simp [refLinkPose]
  · congr 1
    funext i
    rw [Fin.val_succ, refLinkPose_succ, mul_assoc]
    rfl

private theorem prefix_mul_fk (c : LinkFrameChain n) (θ : Fin n → ℝ) (P : RigidTransform) :
    P * (List.ofFn fun i => c.relative i (θ i)).prod =
      (List.ofFn fun i =>
        Twist.exp (Twist.adjoint (P * c.refLinkPose i) (c.jointTwist i)) (θ i)).prod *
        (P * (List.ofFn c.linkRef).prod) := by
  induction n generalizing P with
  | zero => simp
  | succ n ih =>
    have h := ih c.tail (Fin.tail θ) (P * c.linkRef 0)
    rw [twistedMotions_succ, List.prod_cons, List.ofFn_succ, List.prod_cons,
      List.ofFn_succ (f := c.linkRef), List.prod_cons]
    change P * (c.relative 0 (θ 0) *
        (List.ofFn fun i => c.tail.relative i (Fin.tail θ i)).prod) =
      _ * _ * (P * (c.linkRef 0 * (List.ofFn c.tail.linkRef).prod))
    rw [mul_assoc (Twist.exp _ _), ← mul_assoc P (c.linkRef 0), ← h, Twist.exp_adjoint,
      relative]
    group

/-- **K05, adjacent-frame form (MLS eqs. (3.1) and (3.3), pp. 85–87).** Composing the
adjacent link transforms gives the product-of-exponentials forward kinematics of the
base-frame chain with twists `ξᵢ = Ad_{g_{S Lᵢ}(0)} ζᵢ` and `g_st(0) = g_{S Lₙ}(0) g_{Lₙ T}`,
for every real joint vector. This is the book's step from the adjacent-frame product (3.8)
to the product of exponentials with the twists (3.10): MLS p. 94, eqs. (3.7), (3.8), (3.10). -/
theorem fk_eq_toSerialChain_fk (c : LinkFrameChain n) (θ : Fin n → ℝ) :
    c.fk θ = c.toSerialChain.fk θ := by
  have h := c.prefix_mul_fk θ 1
  simp only [one_mul] at h
  simp only [fk, SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, toSerialChain]
  rw [h, mul_assoc]

/-- The derived base-frame chain has the same reference tool pose as the adjacent-frame
composition at `θ = 0` (MLS p. 87, `g_st(0)`). -/
theorem fk_zero (c : LinkFrameChain n) : c.fk 0 = c.toSerialChain.toolRef := by
  rw [fk_eq_toSerialChain_fk, SerialChain.fk_zero]

/-- A revolute joint described in its link frame stays revolute in the base frame, with
the axis moved by the reference link pose (MLS p. 87 and eq. (2.58), p. 55). -/
theorem toSerialChain_isRevoluteJoint (c : LinkFrameChain n) (i : Fin n)
    (hi : (c.jointTwist i).IsRevoluteJoint) :
    (c.toSerialChain.twist i).IsRevoluteJoint :=
  hi.adjoint _

/-- A prismatic joint described in its link frame stays prismatic in the base frame, with
the direction rotated by the reference link pose (MLS p. 87 and eq. (2.58), p. 55). -/
theorem toSerialChain_isPrismaticJoint (c : LinkFrameChain n) (i : Fin n)
    (hi : (c.jointTwist i).IsPrismaticJoint) :
    (c.toSerialChain.twist i).IsPrismaticJoint :=
  hi.adjoint _

end LinkFrameChain

end RoboLean
