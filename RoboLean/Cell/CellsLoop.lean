import RoboLean.Cell.Cells
import RoboLean.Cell.Loop

/-!
# The scene's cells certify the loop

The certified-cells hypothesis `RoboLean.Cell.Loop.CellsCertify` of the sampled loop, discharged for
the scene: for loop data whose waypoints are rational degree points mapped to radians by
`DegPoint.toRad` and whose admission guard implies `SceneLinked`, the cells of the scene certify the
clearance predicate `sceneClear` at the inflation `1/20` rad. The cell of a linked pair is the box
`B.radSet 0` of a scene cell `B` containing both waypoints; its inflation in the sense of
`Loop.inflate` lies in `B.radSet (1/20)`, where `cell_clear` holds. A design statement, not from
MLS; the arm is that of MLS Example 3.2 (pp. 89–91).
-/

noncomputable section

namespace RoboLean.Cell

open RoboLean.Examples

/-- The clearance predicate of the scene at the joint vector `θ` (radians): every point of both
link segments of the arm is at Euclidean distance at least `ρ + c = 9/100` m from every obstacle of
the scene (a design definition, not from MLS). -/
def sceneClear (θ : Fin 3 → ℝ) : Prop :=
  ∀ O ∈ sceneObstacles, KeepsClearance (armLinks armL0 armL1 armL2 θ) O (linkRadius + clearance)

/-- The inflation of a degree box in the sense of the loop lies in the box inflated by the same
radius (a design statement, not from MLS). -/
theorem DegBox.inflate_radSet_subset (B : DegBox) (δ : ℝ) :
    Loop.inflate δ (B.radSet 0) ⊆ B.radSet δ := by
  rintro θ ⟨c, hc, hθc⟩
  exact DegBox.mem_radSet_of_abs_sub_le hc hθc

/-- **The scene's cells certify the loop.** For loop data `P` on three joints with waypoints in
rational degrees, `P.pos w = w.toRad` for every waypoint and an admission guard that implies
`SceneLinked`, every linked pair lies in a common convex cell whose inflation by `1/20` rad
satisfies `sceneClear` (a design statement, not from MLS). -/
theorem sceneCells_certify (P : Loop.Params 3 DegPoint) (hpos : ∀ w, P.pos w = w.toRad)
    (hlinked : ∀ a b, P.linked a b → SceneLinked a b) :
    Loop.CellsCertify P cellInflation sceneClear := by
  intro a b hab
  obtain ⟨B, hB, ha, hb⟩ := hlinked a b hab
  refine ⟨B.radSet 0, B.convex_radSet 0, ?_, ?_, ?_⟩
  · rw [hpos]
    exact DegBox.toRad_mem_radSet ha
  · rw [hpos]
    exact DegBox.toRad_mem_radSet hb
  · intro θ hθ O hO
    exact cell_clear B hB θ (B.inflate_radSet_subset cellInflation hθ) O hO

end RoboLean.Cell
