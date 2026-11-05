import RoboLean.Cell.Geometry
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The pick-and-place scene: arm lengths, obstacles, cells and waypoints

A design scene for the three-link arm of MLS Example 3.2 (pp. 89–91) and Example 4.3 (pp. 172–174),
not from MLS. Lengths in metres in the frame of `elbowArmPosition`: the base yaw axis is the `z`
axis, the table is the plane `z = 0`, the shoulder is at `(0, 0, l₀)`, and at `θ = 0` the arm lies
along `+y`. Joint angles of cells and waypoints are rational numbers of degrees, converted to
radians by `π / 180`.

* Arm: `l₀ = 2/5`, `l₁ = 17/40`, `l₂ = 49/125`; links are capsules of radius `3/50` around the two
  link segments; the required clearance is `3/100`.
* Obstacles: the table `z ≤ 0`; a divider plate `[-1/100, 1/100] × [3/10, 9/10] × [0, 3/10]` in the
  plane `x = 0` between the pick side `x < 0` and the place side `x > 0`; a place shelf
  `[2/5, 19/20] × [0, 3/4] × [0, 3/25]`; a rear wall `y ≤ -1/4`.
* Cells (degree boxes, corners at multiples of 15°): pick `[45, 75] × [-45, 0] × [0, 30]`, cross
  `[-60, 60] × [-45, -30] × [0, 45]`, place `[-75, -45] × [-45, 0] × [0, 15]`.
* Waypoints (degrees): home `(0, -40, 30)`, the lift points `(50, -35, 30)` and `(-50, -35, 15)`,
  pick slots `(50, 0, 30)`, `(60, 0, 30)`, `(70, 0, 30)`, place slots `(-50, 0, 15)`,
  `(-60, 0, 15)`, `(-70, 0, 15)`.
-/

noncomputable section

open Real

namespace RoboLean.Cell

/-- A point of joint space in rational degrees: (base yaw, shoulder, elbow) (a design definition,
not from MLS; the joint order of MLS Example 3.2, p. 90). -/
abbrev DegPoint := ℚ × ℚ × ℚ

/-- Degrees to radians: `q ↦ q π / 180` (a design definition, not from MLS). -/
def degToRad (q : ℚ) : ℝ := (q : ℝ) * π / 180

/-- A degree point as a joint vector in radians, `θ 0, θ 1, θ 2` the base yaw, shoulder and elbow
angles (a design definition, not from MLS). -/
def DegPoint.toRad (w : DegPoint) : Fin 3 → ℝ := ![degToRad w.1, degToRad w.2.1, degToRad w.2.2]

/-- A cell: a box of joint angles given by its lower and upper corners in rational degrees (a design
definition, not from MLS). -/
structure DegBox where
  /-- The lower corner, in degrees. -/
  lo : DegPoint
  /-- The upper corner, in degrees. -/
  hi : DegPoint
  deriving DecidableEq

/-- Membership of a degree point in a degree box, componentwise in rational degrees (a design
definition, not from MLS; decidable). -/
def DegBox.Contains (B : DegBox) (w : DegPoint) : Prop :=
  B.lo.1 ≤ w.1 ∧ w.1 ≤ B.hi.1 ∧ B.lo.2.1 ≤ w.2.1 ∧ w.2.1 ≤ B.hi.2.1 ∧
    B.lo.2.2 ≤ w.2.2 ∧ w.2.2 ≤ B.hi.2.2

instance (B : DegBox) (w : DegPoint) : Decidable (B.Contains w) :=
  inferInstanceAs (Decidable (B.lo.1 ≤ w.1 ∧ w.1 ≤ B.hi.1 ∧ B.lo.2.1 ≤ w.2.1 ∧ w.2.1 ≤ B.hi.2.1 ∧
    B.lo.2.2 ≤ w.2.2 ∧ w.2.2 ≤ B.hi.2.2))

/-- Degrees to radians is monotone (a design statement, not from MLS). -/
theorem degToRad_le_degToRad {a b : ℚ} (h : a ≤ b) : degToRad a ≤ degToRad b := by
  unfold degToRad
  have h' : (a : ℝ) ≤ b := by exact_mod_cast h
  have := Real.pi_pos
  gcongr

/-- The box `B` in radians, inflated by `δ` radians in each joint: the joint vectors `θ` with
`lo i π/180 − δ ≤ θ i ≤ hi i π/180 + δ` for each joint `i` (a design definition, not from MLS). -/
def DegBox.radSet (B : DegBox) (δ : ℝ) : Set (Fin 3 → ℝ) :=
  {θ | ∀ i, B.lo.toRad i - δ ≤ θ i ∧ θ i ≤ B.hi.toRad i + δ}

/-- A degree point contained in a box lies, in radians, in the box without inflation (a design
statement, not from MLS). -/
theorem DegBox.toRad_mem_radSet {B : DegBox} {w : DegPoint} (h : B.Contains w) :
    w.toRad ∈ B.radSet 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  intro i
  fin_cases i <;> simp only [DegPoint.toRad, sub_zero, add_zero] <;> simp <;>
    exact ⟨degToRad_le_degToRad ‹_›, degToRad_le_degToRad ‹_›⟩

/-- An inflated box is convex (a design statement, not from MLS). -/
theorem DegBox.convex_radSet (B : DegBox) (δ : ℝ) : Convex ℝ (B.radSet δ) := by
  intro x hx y hy a b ha hb hab i
  obtain ⟨hx1, hx2⟩ := hx i
  obtain ⟨hy1, hy2⟩ := hy i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : B.lo.toRad i - δ = a * (B.lo.toRad i - δ) + b * (B.lo.toRad i - δ) := by
    rw [← add_mul, hab, one_mul]
  have e2 : B.hi.toRad i + δ = a * (B.hi.toRad i + δ) + b * (B.hi.toRad i + δ) := by
    rw [← add_mul, hab, one_mul]
  constructor
  · rw [e1]
    exact add_le_add (mul_le_mul_of_nonneg_left hx1 ha) (mul_le_mul_of_nonneg_left hy1 hb)
  · rw [e2]
    exact add_le_add (mul_le_mul_of_nonneg_left hx2 ha) (mul_le_mul_of_nonneg_left hy2 hb)

/-- Inflations are nested: `B.radSet δ ⊆ B.radSet δ'` for `δ ≤ δ'` (a design statement, not from
MLS). -/
theorem DegBox.radSet_mono (B : DegBox) {δ δ' : ℝ} (h : δ ≤ δ') : B.radSet δ ⊆ B.radSet δ' := by
  intro θ hθ i
  obtain ⟨h1, h2⟩ := hθ i
  exact ⟨by linarith, by linarith⟩

/-- A joint vector within `δ` radians in each joint of a point of the box lies in the box inflated
by `δ` (a design statement, not from MLS). -/
theorem DegBox.mem_radSet_of_abs_sub_le {B : DegBox} {δ : ℝ} {r θ : Fin 3 → ℝ}
    (hr : r ∈ B.radSet 0) (h : ∀ i, |θ i - r i| ≤ δ) : θ ∈ B.radSet δ := by
  intro i
  obtain ⟨h1, h2⟩ := hr i
  obtain ⟨h3, h4⟩ := abs_le.mp (h i)
  exact ⟨by linarith, by linarith⟩

/-- The convexity step for a move inside a cell: if the box contains the degree points `a` and `b`,
`0 ≤ σ ≤ 1` and `δ ≤ δ'`, then every joint vector within `δ` radians in each joint of
`a + σ (b − a)` (in radians) lies in the box inflated by `δ'` (a design statement, not from MLS). -/
theorem DegBox.mem_radSet_of_near_segment {B : DegBox} {a b : DegPoint} (ha : B.Contains a)
    (hb : B.Contains b) {σ δ δ' : ℝ} (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (hδ : δ ≤ δ')
    {θ : Fin 3 → ℝ} (h : ∀ i, |θ i - (a.toRad i + σ * (b.toRad i - a.toRad i))| ≤ δ) :
    θ ∈ B.radSet δ' := by
  have hr : (fun i => a.toRad i + σ * (b.toRad i - a.toRad i)) ∈ B.radSet 0 := by
    intro i
    obtain ⟨ha1, ha2⟩ := DegBox.toRad_mem_radSet ha i
    obtain ⟨hb1, hb2⟩ := DegBox.toRad_mem_radSet hb i
    have hσ : 0 ≤ 1 - σ := by linarith
    have e : a.toRad i + σ * (b.toRad i - a.toRad i) = (1 - σ) * a.toRad i + σ * b.toRad i := by
      ring
    simp only [sub_zero, add_zero] at ha1 ha2 hb1 hb2 ⊢
    rw [e]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left ha1 hσ, mul_le_mul_of_nonneg_left hb1 hσ₀]
    · nlinarith [mul_le_mul_of_nonneg_left ha2 hσ, mul_le_mul_of_nonneg_left hb2 hσ₀]
  exact B.radSet_mono hδ (DegBox.mem_radSet_of_abs_sub_le hr h)

/-- The base height `l₀ = 2/5` m of the scene's arm (a design value, not from MLS). -/
def armL0 : ℝ := 2 / 5

/-- The upper-arm length `l₁ = 17/40` m of the scene's arm (a design value, not from MLS). -/
def armL1 : ℝ := 17 / 40

/-- The forearm length `l₂ = 49/125` m of the scene's arm, wrist links lumped into the forearm (a
design value, not from MLS). -/
def armL2 : ℝ := 49 / 125

/-- The radius `3/50` m of the capsules around the two link segments (a design value, not from
MLS). -/
def linkRadius : ℝ := 3 / 50

/-- The required clearance `3/100` m between every link capsule and every obstacle (a design value,
not from MLS). -/
def clearance : ℝ := 3 / 100

/-- The inflation `1/20` rad per joint of each cell over which clearance is certified (a design
value, not from MLS). -/
def cellInflation : ℝ := 1 / 20

/-- The closed axis-aligned box `[lo 0, hi 0] × [lo 1, hi 1] × [lo 2, hi 2]` of space, in metres (a
design definition, not from MLS). -/
def realBox (lo hi : Fin 3 → ℝ) : Set (Fin 3 → ℝ) := {p | ∀ i, lo i ≤ p i ∧ p i ≤ hi i}

/-- The table: the closed half-space `z ≤ 0` (a design obstacle, not from MLS; metres). -/
def table : Set (Fin 3 → ℝ) := {p | p 2 ≤ 0}

/-- The divider plate `[-1/100, 1/100] × [3/10, 9/10] × [0, 3/10]` standing on the table in the
plane `x = 0`, between the pick side `x < 0` and the place side `x > 0` (a design obstacle, not from
MLS; metres). -/
def divider : Set (Fin 3 → ℝ) := realBox ![-1 / 100, 3 / 10, 0] ![1 / 100, 9 / 10, 3 / 10]

/-- The place shelf `[2/5, 19/20] × [0, 3/4] × [0, 3/25]` on the side `x > 0` (a design obstacle,
not from MLS; metres). -/
def shelf : Set (Fin 3 → ℝ) := realBox ![2 / 5, 0, 0] ![19 / 20, 3 / 4, 3 / 25]

/-- The rear wall: the closed half-space `y ≤ -1/4` behind the base (a design obstacle, not from
MLS; metres). -/
def rearWall : Set (Fin 3 → ℝ) := {p | p 1 ≤ -1 / 4}

/-- The obstacles of the scene: table, divider, shelf and rear wall (a design list, not from MLS).
-/
def sceneObstacles : List (Set (Fin 3 → ℝ)) := [table, divider, shelf, rearWall]

/-- The pick cell `[45, 75] × [-45, 0] × [0, 30]` in degrees (a design cell, not from MLS). -/
def pickCell : DegBox := ⟨(45, -45, 0), (75, 0, 30)⟩

/-- The crossing cell `[-60, 60] × [-45, -30] × [0, 45]` in degrees, the arm raised above the
divider (a design cell, not from MLS). -/
def crossCell : DegBox := ⟨(-60, -45, 0), (60, -30, 45)⟩

/-- The place cell `[-75, -45] × [-45, 0] × [0, 15]` in degrees (a design cell, not from MLS). -/
def placeCell : DegBox := ⟨(-75, -45, 0), (-45, 0, 15)⟩

/-- The cells of the scene: pick, cross and place (a design list, not from MLS). -/
def sceneCells : List DegBox := [pickCell, crossCell, placeCell]

/-- The joint envelope `[-81, 81] × [-51, 6] × [-6, 51]` in degrees: every cell inflated by `1/10`
rad in each joint lies in it (`radSet_subset_jointEnvelope`; a design box, not from MLS). -/
def jointEnvelope : DegBox := ⟨(-81, -51, -6), (81, 6, 51)⟩

/-- Every cell of the scene inflated by `1/10` rad in each joint lies in the joint envelope (a
design statement, not from MLS; `6° ≥ 1/10` rad because `π ≥ 3`). -/
theorem radSet_subset_jointEnvelope :
    ∀ B ∈ sceneCells, B.radSet (1 / 10) ⊆ jointEnvelope.radSet 0 := by
  have hπ := Real.pi_gt_three
  intro B hB θ hθ i
  simp only [sceneCells, List.mem_cons, List.not_mem_nil, or_false] at hB
  obtain ⟨h1, h2⟩ := hθ i
  rcases hB with rfl | rfl | rfl <;> fin_cases i <;>
    simp [DegPoint.toRad, degToRad, jointEnvelope, pickCell, crossCell, placeCell] at h1 h2 ⊢ <;>
    constructor <;> linarith

/-- The home waypoint `(0, -40, 30)` degrees, in the crossing cell (a design value, not from MLS).
-/
def homeWp : DegPoint := (0, -40, 30)

/-- The lift waypoint over the pick side, `(50, -35, 30)` degrees, in the pick and crossing cells (a
design value, not from MLS). -/
def liftPickWp : DegPoint := (50, -35, 30)

/-- The lift waypoint over the place side, `(-50, -35, 15)` degrees, in the crossing and place cells
(a design value, not from MLS). -/
def liftPlaceWp : DegPoint := (-50, -35, 15)

/-- The pick slots `(50, 0, 30)`, `(60, 0, 30)`, `(70, 0, 30)` degrees, in the pick cell (design
values, not from MLS). -/
def pickSlots : List DegPoint := [(50, 0, 30), (60, 0, 30), (70, 0, 30)]

/-- The place slots `(-50, 0, 15)`, `(-60, 0, 15)`, `(-70, 0, 15)` degrees, in the place cell
(design values, not from MLS). -/
def placeSlots : List DegPoint := [(-50, 0, 15), (-60, 0, 15), (-70, 0, 15)]

/-- All waypoints of the scene: home, the two lift points, the pick slots and the place slots (a
design list, not from MLS). -/
def sceneWaypoints : List DegPoint := [homeWp, liftPickWp, liftPlaceWp] ++ pickSlots ++ placeSlots

/-- Two degree points are linked in the scene when some cell of the scene contains both (a design
definition, not from MLS; decidable). -/
def SceneLinked (a b : DegPoint) : Prop := ∃ B ∈ sceneCells, B.Contains a ∧ B.Contains b

instance (a b : DegPoint) : Decidable (SceneLinked a b) :=
  inferInstanceAs (Decidable (∃ B ∈ sceneCells, B.Contains a ∧ B.Contains b))

/-- Every waypoint of the scene lies in some cell (a design statement, not from MLS; checked by
decision on rationals). -/
theorem sceneWaypoints_mem_cell : ∀ w ∈ sceneWaypoints, ∃ B ∈ sceneCells, B.Contains w := by
  decide

/-- The moves of the pick–lift–cross–descend–place cycle are linked: home to the pick lift, the pick
lift to each pick slot and back, the pick lift to the place lift and back, and the place lift to
each place slot and back (a design statement, not from MLS; checked by decision). -/
theorem cycle_moves_linked :
    SceneLinked homeWp liftPickWp ∧ SceneLinked liftPickWp liftPlaceWp ∧
      SceneLinked liftPlaceWp liftPickWp ∧
      (∀ p ∈ pickSlots, SceneLinked liftPickWp p ∧ SceneLinked p liftPickWp) ∧
      (∀ q ∈ placeSlots, SceneLinked liftPlaceWp q ∧ SceneLinked q liftPlaceWp) := by
  decide

/-- No cell contains a pick slot and a place slot, so a direct move from a pick slot to a place slot
is never linked (a design statement, not from MLS; checked by decision). -/
theorem not_sceneLinked_pick_place : ∀ p ∈ pickSlots, ∀ q ∈ placeSlots, ¬ SceneLinked p q := by
  decide

end RoboLean.Cell
