import RoboLean.Geometry.RotationExp
import RoboLean.Geometry.Rodrigues
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Matrix.Normed

/-!
# Spatial and body angular velocities

MLS printed pp. 51–53, Lemma 2.12, equations (2.46)–(2.52), and Example 2.4.
A real-time rotation curve is differentiated through its matrix entries. The
supplied `HasDerivAt` evidence is required when defining angular velocity; a
pointwise rotation and an arbitrary matrix do not suffice. Point trajectories
below describe pure rotation about a common origin, with constant body
coordinates. Body-expressed physical velocity is not the derivative of those
constant coordinates.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean
namespace Rotation

variable {R : ℝ → Rotation} {A : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}

/-- Transposing the matrix derivative of a rotation curve. -/
theorem hasDerivAt_val_transpose
    (hR : HasDerivAt (fun s => (R s).val) A t) :
    HasDerivAt (fun s => (R s).valᵀ) Aᵀ t := by
  let L := (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℝ ℝ).toLinearMap.toContinuousLinearMap
  exact L.hasFDerivAt.comp_hasDerivAt t hR

/-- Differentiating `R Rᵀ = I` gives the spatial skew matrix. -/
theorem spatialVelocity_skew
    (hR : HasDerivAt (fun s => (R s).val) A t) :
    (A * (R t).valᵀ)ᵀ = -(A * (R t).valᵀ) := by
  have h := hR.mul (hasDerivAt_val_transpose hR)
  change HasDerivAt (fun s => (R s).val * (R s).valᵀ)
    (A * (R t).valᵀ + (R t).val * Aᵀ) t at h
  have hc : HasDerivAt (fun _ : ℝ => (1 : Matrix (Fin 3) (Fin 3) ℝ))
      (A * (R t).valᵀ + (R t).val * Aᵀ) t := by
    simpa only [Pi.mul_apply, mul_transpose] using h
  have hz := hc.unique (hasDerivAt_const t (1 : Matrix (Fin 3) (Fin 3) ℝ))
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  exact eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using hz)

/-- Differentiating `Rᵀ R = I` gives the body skew matrix. -/
theorem bodyVelocity_skew
    (hR : HasDerivAt (fun s => (R s).val) A t) :
    ((R t).valᵀ * A)ᵀ = -((R t).valᵀ * A) := by
  have h := (hasDerivAt_val_transpose hR).mul hR
  change HasDerivAt (fun s => (R s).valᵀ * (R s).val)
    (Aᵀ * (R t).val + (R t).valᵀ * A) t at h
  have hc : HasDerivAt (fun _ : ℝ => (1 : Matrix (Fin 3) (Fin 3) ℝ))
      (Aᵀ * (R t).val + (R t).valᵀ * A) t := by
    simpa only [Pi.mul_apply, transpose_mul] using h
  have hz := hc.unique (hasDerivAt_const t (1 : Matrix (Fin 3) (Fin 3) ℝ))
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  exact eq_neg_iff_add_eq_zero.mpr hz

/-- MLS (2.48): spatial angular velocity, requiring actual derivative evidence. -/
def spatialAngularVelocity (R : ℝ → Rotation) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (t : ℝ) (hR : HasDerivAt (fun s => (R s).val) A t) : Vec3 :=
  Vec3.hatLinearEquiv.symm
    ⟨A * (R t).valᵀ, (mem_skewMatrix3_iff _).mpr (spatialVelocity_skew hR)⟩

/-- MLS (2.49): body angular velocity in the instantaneous body frame. -/
def bodyAngularVelocity (R : ℝ → Rotation) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (t : ℝ) (hR : HasDerivAt (fun s => (R s).val) A t) : Vec3 :=
  Vec3.hatLinearEquiv.symm
    ⟨(R t).valᵀ * A, (mem_skewMatrix3_iff _).mpr (bodyVelocity_skew hR)⟩

@[simp] theorem hat_spatialAngularVelocity
    (hR : HasDerivAt (fun s => (R s).val) A t) :
    Vec3.hat (spatialAngularVelocity R A t hR) = A * (R t).valᵀ :=
  Vec3.hat_vee _ (spatialVelocity_skew hR)

@[simp] theorem hat_bodyAngularVelocity
    (hR : HasDerivAt (fun s => (R s).val) A t) :
    Vec3.hat (bodyAngularVelocity R A t hR) = (R t).valᵀ * A :=
  Vec3.hat_vee _ (bodyVelocity_skew hR)

/-- MLS (2.50): rotate spatial angular velocity into the instantaneous body frame. -/
theorem bodyAngularVelocity_eq
    (hR : HasDerivAt (fun s => (R s).val) A t) :
    bodyAngularVelocity R A t hR = (R t)⁻¹.act (spatialAngularVelocity R A t hR) := by
  apply Vec3.hatLinearEquiv.injective
  apply Subtype.ext
  change Vec3.hat (bodyAngularVelocity R A t hR) =
    Vec3.hat ((R t)⁻¹.act (spatialAngularVelocity R A t hR))
  rw [hat_bodyAngularVelocity, Vec3.hat_act, hat_spatialAngularVelocity,
    inv_val, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc, transpose_mul, Matrix.mul_one]

/-- MLS (2.46): the velocity of a point with constant body coordinates. -/
theorem hasDerivAt_act
    (hR : HasDerivAt (fun s => (R s).val) A t) (q : Vec3) :
    HasDerivAt (fun s => (R s).act q) (Matrix.toEuclideanLin A q) t := by
  let L : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] Vec3 :=
    (LinearMap.applyₗ (R := ℝ) (M₂ := Vec3) q).comp Matrix.toEuclideanLin.toLinearMap
  exact L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hR

/-- MLS (2.47) and (2.51): spatial point velocity is angular velocity cross
current spatial position. This is pure rotation about the common origin. -/
theorem spatial_velocity_eq_cross
    (hR : HasDerivAt (fun s => (R s).val) A t) (q : Vec3) :
    Matrix.toEuclideanLin A q =
      Vec3.cross (spatialAngularVelocity R A t hR) ((R t).act q) := by
  apply WithLp.ofLp_injective
  change A *ᵥ WithLp.ofLp q =
    WithLp.ofLp (Vec3.cross (spatialAngularVelocity R A t hR) ((R t).act q))
  rw [← Vec3.hat_mulVec, hat_spatialAngularVelocity]
  change A *ᵥ WithLp.ofLp q =
    (A * (R t).valᵀ) *ᵥ ((R t).val *ᵥ WithLp.ofLp q)
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, transpose_mul, Matrix.mul_one]

/-- The actual spatial trajectory has the velocity in MLS (2.51). -/
theorem hasDerivAt_act_spatial
    (hR : HasDerivAt (fun s => (R s).val) A t) (q : Vec3) :
    HasDerivAt (fun s => (R s).act q)
      (Vec3.cross (spatialAngularVelocity R A t hR) ((R t).act q)) t :=
  (hasDerivAt_act hR q).congr_deriv (spatial_velocity_eq_cross hR q)

/-- MLS (2.52): express physical velocity in body coordinates. The fixed
body coordinate `q` itself has zero derivative, which is a different quantity. -/
theorem body_velocity_eq_cross
    (hR : HasDerivAt (fun s => (R s).val) A t) (q : Vec3) :
    (R t)⁻¹.act (Matrix.toEuclideanLin A q) =
      Vec3.cross (bodyAngularVelocity R A t hR) q := by
  rw [spatial_velocity_eq_cross hR q, act_cross, ← bodyAngularVelocity_eq hR,
    inv_act_act]

/-- Time reparameterization of a fixed-axis exponential, with arbitrary
instantaneous signed scalar rate. -/
theorem hasDerivAt_exp_val_comp (ω : Vec3) {θ : ℝ → ℝ} {θ' t : ℝ}
    (hθ : HasDerivAt θ θ' t) :
    HasDerivAt (fun s => (exp ω (θ s)).val)
      (θ' • (Vec3.hat ω * (exp ω (θ t)).val)) t :=
  (hasDerivAt_exp_val ω (θ t)).scomp t hθ

/-- The spatial angular velocity of a time-reparameterized fixed-axis motion. -/
theorem spatialAngularVelocity_exp (ω : Vec3) {θ : ℝ → ℝ} {θ' t : ℝ}
    (hθ : HasDerivAt θ θ' t) :
    spatialAngularVelocity (fun s => exp ω (θ s))
      (θ' • (Vec3.hat ω * (exp ω (θ t)).val)) t
      (hasDerivAt_exp_val_comp ω hθ) = θ' • ω := by
  apply Vec3.hatLinearEquiv.injective
  apply Subtype.ext
  change Vec3.hat (spatialAngularVelocity _ _ _ _) = Vec3.hat (θ' • ω)
  rw [hat_spatialAngularVelocity, Vec3.hat_smul, Matrix.smul_mul,
    Matrix.mul_assoc, mul_transpose, Matrix.mul_one]

/-- For this fixed-axis motion, body and spatial angular velocities agree.
This equality is special to this motion; it is not asserted for arbitrary curves. -/
theorem bodyAngularVelocity_exp (ω : Vec3) {θ : ℝ → ℝ} {θ' t : ℝ}
    (hθ : HasDerivAt θ θ' t) :
    bodyAngularVelocity (fun s => exp ω (θ s))
      (θ' • (Vec3.hat ω * (exp ω (θ t)).val)) t
      (hasDerivAt_exp_val_comp ω hθ) = θ' • ω := by
  have hcomm : Vec3.hat ω * (exp ω (θ t)).val =
      (exp ω (θ t)).val * Vec3.hat ω :=
    (((Commute.refl (Vec3.hat ω)).smul_right (θ t)).exp_right).eq
  apply Vec3.hatLinearEquiv.injective
  apply Subtype.ext
  change Vec3.hat (bodyAngularVelocity _ _ _ _) = Vec3.hat (θ' • ω)
  rw [hat_bodyAngularVelocity, Vec3.hat_smul, Matrix.mul_smul, hcomm,
    ← Matrix.mul_assoc, transpose_mul, Matrix.one_mul]

/-- The positive unit z-axis in the established right-handed coordinates. -/
def zAxis : Vec3 := WithLp.toLp 2 ![0, 0, 1]

private theorem norm_zAxis : ‖zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [zAxis, Fin.sum_univ_succ]

/-- The fixed positive z-axis rotation used in MLS Example 2.4. -/
def zRotation (θ : ℝ) : Rotation := exp zAxis θ

/-- The actual exponential equals the independently displayed `Rz` matrix,
fixing the sine signs used in MLS printed p. 53. -/
theorem zRotation_val (θ : ℝ) :
    (zRotation θ).val =
      !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1] := by
  rw [zRotation, exp_val, Vec3.exp_hat_of_norm_eq_one _ norm_zAxis]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zAxis, Vec3.hat, pow_two]

/-- MLS Example 2.4, for every differentiable angle trajectory: both angular
velocities are `(0,0,θ')`. The displayed matrix family is `zRotation_val`. -/
theorem zRotation_angularVelocities {θ : ℝ → ℝ} {θ' t : ℝ}
    (hθ : HasDerivAt θ θ' t) :
    let R : ℝ → Rotation := fun s => zRotation (θ s)
    let A := θ' • (Vec3.hat zAxis * (zRotation (θ t)).val)
    let hR : HasDerivAt (fun s => (R s).val) A t := hasDerivAt_exp_val_comp zAxis hθ
    spatialAngularVelocity R A t hR = WithLp.toLp 2 ![0, 0, θ'] ∧
      bodyAngularVelocity R A t hR = WithLp.toLp 2 ![0, 0, θ'] := by
  dsimp only [zRotation]
  constructor
  · rw [spatialAngularVelocity_exp zAxis hθ]
    ext i
    fin_cases i <;> simp [zAxis]
  · rw [bodyAngularVelocity_exp zAxis hθ]
    ext i
    fin_cases i <;> simp [zAxis]

end Rotation
end RoboLean
