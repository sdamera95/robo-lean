import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

namespace RoboLean

theorem add_sq (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring


#print axioms add_sq

end RoboLean
