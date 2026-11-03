import RoboLean.LieGroups.ExponentialClosedForms
import RoboLean.Geometry.RotationLog

/-!
# The log function on `SE(3)` of Example A.15 inverts the exponential

MLS Appendix A, printed pp. 413–414. After Example A.12 the book says that there is a function
`log : U → g` with `exp ∘ log (g) = g`, "the inverse of `exp`"; Example A.14 gives the log function
on `SO(3)` (`2 cos θ + 1 = trace R`, `ω̂ = (R − Rᵀ)/(2 sin θ)` for `R ≠ I`) and Example A.15 the log
function on `SE(3)`:
`log (R, p) = (A⁻¹p, ω)` with `ω̂ = log R` and the printed `A⁻¹`; "if `ω = 0` then `A = I`", and
"the log function on `SE(3)` is multi-valued since `ω` is not unique".

Statements. For every choice of `ω` with `e^{ω̂} = R` and `sin ‖ω‖ ≠ 0`, the twist
`(A⁻¹p, ω)` has `exp = (R, p)` (`exp_logOfAngular`); for `R = I` the twist `(p, 0)` does
(`exp_logOfAngular_zero`). With the principal angle `θ = arccos((trace R − 1)/2) ∈ [0, π]` and
the axis of Example A.14 (the library's `Rotation.genericAxis`), the single-valued choice
`Twist.seLog` inverts the exponential wherever `sin θ ≠ 0`, that is, for every rotation other
than `I` and the rotations by `π` (`exp_seLog`).

Added hypothesis: `sin ‖ω‖ ≠ 0`. The book prints `A⁻¹` under `ω ≠ 0`, but its denominator vanishes
when `‖ω‖` is a nonzero multiple of `π` (the corrected printing recorded with
`Twist.expTranslationMatrixInv`). Coordinates `(v, ω)`; the exponential is the library's
`Twist.exp ξ 1`.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace Twist

/-- The twist `(A⁻¹p, ω)` of MLS Example A.15, printed p. 414, for a pose with translation `p` and a
chosen rotation vector `ω` (with `ω̂ = log R`); `A⁻¹` is the printed matrix
`expTranslationMatrixInv ω`. Coordinates `(v, ω)`. -/
def logOfAngular (g : RigidTransform) (ω : Vec3) : Twist :=
  ⟨WithLp.toLp 2 (expTranslationMatrixInv ω *ᵥ WithLp.ofLp g.translation), ω⟩

/-- **MLS Example A.15, p. 414: the log function on `SE(3)` inverts the exponential.** If
`e^{ω̂} = R` and `sin ‖ω‖ ≠ 0`, then `exp (A⁻¹p, ω)^ = (R, p)`. The hypothesis `sin ‖ω‖ ≠ 0` is
added (the book prints `ω ≠ 0`). Any `ω` with `e^{ω̂} = R` may be used ("multi-valued"). -/
theorem exp_logOfAngular (g : RigidTransform) (ω : Vec3) (hR : Rotation.exp ω 1 = g.rotation)
    (hs : Real.sin ‖ω‖ ≠ 0) : exp (logOfAngular g ω) 1 = g := by
  have hω : ω ≠ 0 := by
    rintro rfl
    rw [norm_zero, Real.sin_zero] at hs
    exact hs rfl
  ext1
  · rw [exp_rotation]
    exact hR
  · rw [exp_one_translation _ hω]
    change WithLp.toLp 2 (expTranslationMatrix ω *ᵥ (expTranslationMatrixInv ω *ᵥ
      WithLp.ofLp g.translation)) = g.translation
    rw [Matrix.mulVec_mulVec, expTranslationMatrix_mul_inv ω hs, Matrix.one_mulVec]

/-- **MLS Example A.15, p. 414: "If `ω = 0` then `A = I`."** For a pure translation `(I, p)` the
twist `(p, 0)` has `exp (p, 0)^ = (I, p)`. -/
theorem exp_logOfAngular_zero (g : RigidTransform) (hR : g.rotation = 1) :
    exp ⟨g.translation, 0⟩ 1 = g := by
  rw [exp_pure_translation, one_smul]
  ext1
  · exact hR.symm
  · rfl

/-- The single-valued log function on `SE(3)` built from MLS Examples A.14 and A.15, printed p. 414:
`ω = θ ω₀` with the principal angle `θ = arccos((trace R − 1)/2)` (eq. (2.17)) and the axis
`ω₀ = (R − Rᵀ)^∨/(2 sin θ)` (eq. (2.18), `Rotation.genericAxis`), and translation coordinates
`A⁻¹p`. It is the inverse of `exp` where `sin θ ≠ 0` (`exp_seLog`). Coordinates `(v, ω)`. -/
def seLog (g : RigidTransform) : Twist :=
  logOfAngular g (Rotation.principalAngle g.rotation • Rotation.genericAxis g.rotation)

/-- **MLS Examples A.14–A.15, p. 414: `exp ∘ log (g) = g`** for every pose whose rotation has
principal angle `θ` with `sin θ ≠ 0`, that is, every rotation other than `I` and the rotations by
`π` (MLS p. 413: "there is a function `log : U → g` such that `exp ∘ log (g) = g`"). -/
theorem exp_seLog (g : RigidTransform) (hs : Real.sin (Rotation.principalAngle g.rotation) ≠ 0) :
    exp (seLog g) 1 = g := by
  obtain ⟨hn, hR⟩ := Rotation.genericAxis_spec g.rotation hs
  have hθ := Rotation.principalAngle_mem_Icc g.rotation
  have hnorm : ‖Rotation.principalAngle g.rotation • Rotation.genericAxis g.rotation‖ =
      Rotation.principalAngle g.rotation := by
    rw [norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_nonneg hθ.1]
  apply exp_logOfAngular
  · refine Eq.trans ?_ hR
    apply Subtype.ext
    simp only [Rotation.exp_val, one_smul, Vec3.hat_smul]
  · rw [hnorm]
    exact hs

end Twist
end RoboLean
