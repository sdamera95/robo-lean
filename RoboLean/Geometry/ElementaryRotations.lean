import RoboLean.Geometry.RotationVelocity

/-!
# Elementary rotations about the positive coordinate axes

MLS printed p. 31 displays `Rx`, `Ry`, and `Rz` with column-vector,
right-handed conventions. The matrix families below are written independently
and then identified with the actual matrix exponential for every real angle.
The existing `zAxis` and `zRotation` family are reused without redefinition.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean
namespace Rotation

/-- The positive unit x-axis. -/
def xAxis : Vec3 := WithLp.toLp 2 ![1, 0, 0]

/-- The positive unit y-axis. -/
def yAxis : Vec3 := WithLp.toLp 2 ![0, 1, 0]

@[simp] theorem norm_xAxis : ‖xAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [xAxis, Fin.sum_univ_succ]

@[simp] theorem norm_yAxis : ‖yAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [yAxis, Fin.sum_univ_succ]

/-- The independently displayed `Rx(θ)` from MLS printed p. 31. -/
def xMatrix (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, Real.cos θ, -Real.sin θ; 0, Real.sin θ, Real.cos θ]

/-- The independently displayed `Ry(θ)` from MLS printed p. 31. -/
def yMatrix (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, 0, Real.sin θ; 0, 1, 0; -Real.sin θ, 0, Real.cos θ]

/-- The independently displayed `Rz(θ)` from MLS printed p. 31. -/
def zMatrix (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]

/-- The x-axis matrix family equals the actual exponential at every real angle. -/
theorem exp_xAxis_val (θ : ℝ) : (exp xAxis θ).val = xMatrix θ := by
  rw [exp_val, Vec3.exp_hat_of_norm_eq_one _ norm_xAxis]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xMatrix, xAxis, Vec3.hat, pow_two]

/-- The y-axis matrix family equals the actual exponential at every real angle. -/
theorem exp_yAxis_val (θ : ℝ) : (exp yAxis θ).val = yMatrix θ := by
  rw [exp_val, Vec3.exp_hat_of_norm_eq_one _ norm_yAxis]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [yMatrix, yAxis, Vec3.hat, pow_two]

/-- Reuse the existing actual-exponential equality for the z-axis family. -/
theorem exp_zAxis_val (θ : ℝ) : (exp zAxis θ).val = zMatrix θ :=
  zRotation_val θ

/-- Each displayed x-axis matrix is a proper rotation, with determinant `+1`. -/
theorem xMatrix_mem (θ : ℝ) : xMatrix θ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [← exp_xAxis_val]
  exact (exp xAxis θ).property

/-- Each displayed y-axis matrix is a proper rotation, with determinant `+1`. -/
theorem yMatrix_mem (θ : ℝ) : yMatrix θ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [← exp_yAxis_val]
  exact (exp yAxis θ).property

/-- Each displayed z-axis matrix is a proper rotation, with determinant `+1`. -/
theorem zMatrix_mem (θ : ℝ) : zMatrix θ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [← exp_zAxis_val]
  exact (exp zAxis θ).property

/-- The coordinate-defined x-axis rotation. -/
def xRotation (θ : ℝ) : Rotation := ⟨xMatrix θ, xMatrix_mem θ⟩

/-- The coordinate-defined y-axis rotation. -/
def yRotation (θ : ℝ) : Rotation := ⟨yMatrix θ, yMatrix_mem θ⟩

@[simp] theorem xRotation_val (θ : ℝ) : (xRotation θ).val = xMatrix θ := rfl

@[simp] theorem yRotation_val (θ : ℝ) : (yRotation θ).val = yMatrix θ := rfl

/-- The existing z rotation has the same independently displayed coordinate matrix. -/
theorem zRotation_matrix (θ : ℝ) : (zRotation θ).val = zMatrix θ := zRotation_val θ

/-- Equality of the actual exponential and the coordinate-defined x rotation. -/
theorem exp_xAxis (θ : ℝ) : exp xAxis θ = xRotation θ :=
  Subtype.ext (exp_xAxis_val θ)

/-- Equality of the actual exponential and the coordinate-defined y rotation. -/
theorem exp_yAxis (θ : ℝ) : exp yAxis θ = yRotation θ :=
  Subtype.ext (exp_yAxis_val θ)

/-- All three elementary matrix families preserve orientation at every real angle. -/
theorem elementary_matrix_det (θ : ℝ) :
    (xMatrix θ).det = 1 ∧ (yMatrix θ).det = 1 ∧ (zMatrix θ).det = 1 :=
  ⟨(xMatrix_mem θ).2, (yMatrix_mem θ).2, (zMatrix_mem θ).2⟩

/-- Positive quarter-turn about x sends the positive y-axis to the positive z-axis. -/
theorem xRotation_pi_div_two_act_y : (xRotation (Real.pi / 2)).act yAxis = zAxis := by
  apply WithLp.ofLp_injective
  change xMatrix (Real.pi / 2) *ᵥ WithLp.ofLp yAxis = WithLp.ofLp zAxis
  ext i
  fin_cases i <;> norm_num [xMatrix, yAxis, zAxis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Positive quarter-turn about y sends the positive z-axis to the positive x-axis. -/
theorem yRotation_pi_div_two_act_z : (yRotation (Real.pi / 2)).act zAxis = xAxis := by
  apply WithLp.ofLp_injective
  change yMatrix (Real.pi / 2) *ᵥ WithLp.ofLp zAxis = WithLp.ofLp xAxis
  ext i
  fin_cases i <;> norm_num [yMatrix, zAxis, xAxis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Positive quarter-turn about z sends the positive x-axis to the positive y-axis. -/
theorem zRotation_pi_div_two_act_x : (zRotation (Real.pi / 2)).act xAxis = yAxis := by
  apply WithLp.ofLp_injective
  change (zRotation (Real.pi / 2)).val *ᵥ WithLp.ofLp xAxis = WithLp.ofLp yAxis
  rw [zRotation_matrix]
  ext i
  fin_cases i <;> norm_num [zMatrix, xAxis, yAxis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end Rotation
end RoboLean
