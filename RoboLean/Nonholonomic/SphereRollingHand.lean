import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The grasp constraint as a control system: MLS (8.30)–(8.31)

MLS Chapter 8, §4.1, printed pp. 382–383: the constraints of a grasp with rolling contacts
`J_h(θ, x) θ̇ = Gᵀ(θ, x) ẋ` (8.30); "If we let `u₁` be an input which controls the velocity of the
object and let `u₂` parameterize the internal motions, then equation (8.30) can be written as
`ẋ = u₁`, `θ̇ = J_h⁺ Gᵀ u₁ + K u₂` (8.31), where the columns of `K` span the null space of `J_h`."

**What is formalized.** At a fixed configuration, with matrices `J = J_h`, `Gt = Gᵀ`, a matrix `Jp`
standing for `J_h⁺` and `K`: if `J Jp Gᵀ = Gᵀ` and the columns of `K` lie in and span the null
space of `J`, the velocities `(θ̇, ẋ)` satisfying (8.30) are exactly those of the form (8.31). The
condition `J Jp Gᵀ = Gᵀ` is not printed; it holds for the Moore–Penrose inverse `J_h⁺` when the
grasp is manipulable (every `Gᵀ ẋ` lies in the range of `J_h`, p. 382), and for any right inverse
of `J_h`. The book's matrices depend on `(θ, x)`; the statement holds at each configuration.
-/

open Matrix

namespace RoboLean
namespace Nonholonomic

variable {k n p r : Type*} [Fintype k] [Fintype n] [Fintype p] [Fintype r]

/-- **MLS eqs. (8.30)–(8.31), pp. 382–383: the grasp constraint as a control system.** If
`J Jp Gᵀ = Gᵀ`, `J K = 0` and every null vector of `J` is `K v` for some `v`, then
`J θ̇ = Gᵀ ẋ` holds exactly when `ẋ = u₁` and `θ̇ = Jp Gᵀ u₁ + K u₂` for some inputs `u₁, u₂`. -/
theorem grasp_constraint_iff_control {J : Matrix k n ℝ} {Gt : Matrix k p ℝ} {Jp : Matrix n k ℝ}
    {K : Matrix n r ℝ} (hJp : J * Jp * Gt = Gt) (hK : J * K = 0)
    (hspan : ∀ w : n → ℝ, J *ᵥ w = 0 → ∃ v : r → ℝ, w = K *ᵥ v) (θ' : n → ℝ) (x' : p → ℝ) :
    J *ᵥ θ' = Gt *ᵥ x' ↔
      ∃ (u₁ : p → ℝ) (u₂ : r → ℝ), x' = u₁ ∧ θ' = Jp *ᵥ (Gt *ᵥ u₁) + K *ᵥ u₂ := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := hspan (θ' - Jp *ᵥ (Gt *ᵥ x')) (by
      rw [mulVec_sub, h, mulVec_mulVec, mulVec_mulVec, hJp, sub_self])
    exact ⟨x', v, rfl, by rw [← hv]; abel⟩
  · rintro ⟨u₁, u₂, rfl, rfl⟩
    rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, hJp, mulVec_mulVec, hK, zero_mulVec, add_zero]

/-- **MLS p. 383, special case 2: internal motions.** With the object held fixed (`ẋ = u₁ = 0`),
the finger velocities allowed by (8.30) are exactly `θ̇ = K u₂`, under the hypotheses of
`grasp_constraint_iff_control`. -/
theorem grasp_constraint_fixed_iff {J : Matrix k n ℝ} {Gt : Matrix k p ℝ} {Jp : Matrix n k ℝ}
    {K : Matrix n r ℝ} (hJp : J * Jp * Gt = Gt) (hK : J * K = 0)
    (hspan : ∀ w : n → ℝ, J *ᵥ w = 0 → ∃ v : r → ℝ, w = K *ᵥ v) (θ' : n → ℝ) :
    J *ᵥ θ' = Gt *ᵥ 0 ↔ ∃ u₂ : r → ℝ, θ' = K *ᵥ u₂ := by
  rw [grasp_constraint_iff_control hJp hK hspan]
  constructor
  · rintro ⟨u₁, u₂, rfl, h⟩
    exact ⟨u₂, by simpa using h⟩
  · rintro ⟨u₂, rfl⟩
    exact ⟨0, u₂, rfl, by simp⟩

end Nonholonomic
end RoboLean
