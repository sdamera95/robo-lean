import RoboLean.Kinematics.SphericalWrist
import RoboLean.Examples.ElbowManipulator

/-!
# The elbow manipulator has a spherical wrist: its dextrous and reachable workspaces agree

MLS Chapter 3, printed p. 96: "A common feature of industrial manipulators is to place a spherical
wrist at the end of the manipulator, as in the elbow manipulator given in Example 3.2." The elbow
manipulator of Example 3.2 (pp. 89–90, `Examples.elbowManipulator`) has wrist axes `+z`, `-x`,
`+y` through the wrist centre `(0, l₁ + l₂, l₀)`, which is the tool position of `g_st(0)`; so it
satisfies the hypotheses of the spherical-wrist workspace theorems for all real link lengths, and
`W_D = W_R`, `W = W_R × SO(3)` hold for it with unrestricted joints. Lean joint `i` is the book's
joint `i + 1`; the wrist joints are Lean joints `3, 4, 5`.
-/

noncomputable section

namespace RoboLean
namespace Examples

open RoboLean.Rotation (xAxis yAxis zAxis)

/-- **MLS p. 96 with Example 3.2 (pp. 89–90): the elbow manipulator's wrist is spherical.** Its last
three joints are revolute about the unit axes `+z`, `-x`, `+y` (consecutively orthogonal, in fact
mutually orthogonal) through the reference tool position `(0, l₁ + l₂, l₀)`, for all real
`l₀, l₁, l₂`. -/
theorem elbowManipulator_hasSphericalWrist (l₀ l₁ l₂ : ℝ) :
    SerialChain.HasSphericalWrist (n := 3) (elbowManipulator l₀ l₁ l₂) ![zAxis, -xAxis, yAxis] := by
  have hz : ‖zAxis‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [zAxis, Fin.sum_univ_succ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [hz]
  · simp [zAxis, xAxis, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  · simp [yAxis, xAxis, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  · intro i
    fin_cases i <;> rfl

/-- **MLS p. 96: `W_D = W_R` for the elbow manipulator of Example 3.2** (unrestricted joints, all real
link lengths). -/
theorem elbowManipulator_dextrousWorkspace_eq (l₀ l₁ l₂ : ℝ) :
    (elbowManipulator l₀ l₁ l₂).dextrousWorkspace Set.univ =
      (elbowManipulator l₀ l₁ l₂).reachableWorkspace Set.univ :=
  (elbowManipulator_hasSphericalWrist l₀ l₁ l₂).dextrousWorkspace_eq

/-- **MLS p. 96: `W = W_R × SO(3)` for the elbow manipulator of Example 3.2** (unrestricted joints,
all real link lengths). -/
theorem elbowManipulator_completeWorkspace_eq (l₀ l₁ l₂ : ℝ) :
    (elbowManipulator l₀ l₁ l₂).completeWorkspace Set.univ =
      {g | g.translation ∈ (elbowManipulator l₀ l₁ l₂).reachableWorkspace Set.univ} :=
  (elbowManipulator_hasSphericalWrist l₀ l₁ l₂).completeWorkspace_eq

end Examples
end RoboLean
