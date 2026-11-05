import RoboLean.Cell.CellsLoop
import RoboLean.Cell.SupervisorInstances

/-!
# The scene's cells and the executable supervisor's cells

The executable cell supervisor stores its cells as rational degree boxes
(`RoboLean.Cell.Supervisor.Box`) and links two waypoints when some box of its list contains both
(`RoboLean.Cell.Supervisor.CellLinked`). Its instance data `Supervisor.Instances.params` holds the
same three boxes as the scene (`pickCell`, `crossCell`, `placeCell`, the same rational corners in
degrees), and a degree box contains a waypoint in the scene's sense exactly when it does in the
supervisor's sense (the same six inequalities over `ℚ`). Hence the supervisor's link relation on its
instance cells is `SceneLinked`, and the scene's cells certify the loop for loop data whose guard is
that relation. A design statement, not from MLS.
-/

noncomputable section

namespace RoboLean.Cell

/-- A degree box of the scene as a box of the executable supervisor, with the same corners in
degrees (a design definition, not from MLS). -/
def DegBox.toSupervisorBox (B : DegBox) : Supervisor.Box := ⟨B.lo, B.hi⟩

/-- A degree box contains a waypoint in the scene's sense exactly when its supervisor box does: the
same six inequalities over `ℚ` in degrees (a design statement, not from MLS). -/
theorem DegBox.contains_iff_mem (B : DegBox) (w : DegPoint) :
    B.Contains w ↔ B.toSupervisorBox.Mem w := Iff.rfl

/-- The supervisor's instance cells are the scene's cells, box by box with the same corners (a
design statement, not from MLS). -/
theorem sceneCells_toSupervisorBox :
    sceneCells.map DegBox.toSupervisorBox = Supervisor.Instances.params.cells := rfl

/-- The scene's link relation is the supervisor's link relation on its instance cells (a design
statement, not from MLS). -/
theorem sceneLinked_iff_cellLinked (a b : DegPoint) :
    SceneLinked a b ↔ Supervisor.CellLinked Supervisor.Instances.params.cells a b := by
  rw [← sceneCells_toSupervisorBox]
  simp only [SceneLinked, Supervisor.CellLinked, List.mem_map]
  constructor
  · rintro ⟨B, hB, ha, hb⟩
    exact ⟨B.toSupervisorBox, ⟨B, hB, rfl⟩, ha, hb⟩
  · rintro ⟨c, ⟨B, hB, rfl⟩, ha, hb⟩
    exact ⟨B, hB, ha, hb⟩

/-- The executable link test on the supervisor's instance cells decides `SceneLinked` (a design
statement, not from MLS). -/
theorem linked_eq_true_iff_sceneLinked (a b : DegPoint) :
    Supervisor.linked Supervisor.Instances.params.cells a b = true ↔ SceneLinked a b := by
  rw [Supervisor.linked_eq_true_iff, sceneLinked_iff_cellLinked]

/-- **The scene's cells certify the loop with the supervisor's guard.** For loop data `P` on three
joints with `P.pos w = w.toRad` and a guard that implies the supervisor's link relation on its
instance cells, the cells certify `sceneClear` at the inflation `1/20` rad (a design statement,
not from MLS). -/
theorem sceneCells_certify_of_cellLinked (P : Loop.Params 3 DegPoint)
    (hpos : ∀ w, P.pos w = w.toRad)
    (hlinked : ∀ a b, P.linked a b → Supervisor.CellLinked Supervisor.Instances.params.cells a b) :
    Loop.CellsCertify P cellInflation sceneClear :=
  sceneCells_certify P hpos fun a b h => (sceneLinked_iff_cellLinked a b).2 (hlinked a b h)

end RoboLean.Cell
