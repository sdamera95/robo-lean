import RoboLean.Geometry.RigidVelocity
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Matrix.Normed

/-!
# Composition and reversal of rigid-body velocities

MLS printed pp. 58–59, Propositions 2.14–2.15, compose spatial and body
velocities of compatible frame curves. Equations (2.62)–(2.63) specialize
to a constant change of spatial reference. Printed p. 61, Lemma 2.16,
reverses the frame direction (ledger X41–X43 and X46).

Every velocity below carries an actual `HasDerivAt` proof for its homogeneous
pose curve. Product and inverse derivatives are proved by the corresponding
calculus rules; no desired velocity identity is assumed. The curves take
values in proper rigid transforms. Frame labels and physical units remain
external conventions, and all derivatives are at a real time in the full
real domain rather than one-sided derivatives at a domain boundary.
-/

noncomputable section

open scoped Matrix.Norms.Operator

namespace RoboLean
namespace RigidTransform

private theorem homogeneous_mul_inv_assoc (g : RigidTransform) (A : HomogeneousMatrix) :
    g.toHomogeneous * ((g⁻¹).toHomogeneous * A) = A := by
  rw [← mul_assoc, toHomogeneous_mul_inv, one_mul]

private theorem homogeneous_inv_mul_assoc (g : RigidTransform) (A : HomogeneousMatrix) :
    (g⁻¹).toHomogeneous * (g.toHomogeneous * A) = A := by
  rw [← mul_assoc, toHomogeneous_inv_mul, one_mul]

/-- The actual homogeneous derivative of a composed pose curve. -/
theorem hasDerivAt_toHomogeneous_mul
    {g h : ℝ → RigidTransform} {D E : HomogeneousMatrix} {t : ℝ}
    (hg : HasDerivAt (fun s => (g s).toHomogeneous) D t)
    (hh : HasDerivAt (fun s => (h s).toHomogeneous) E t) :
    HasDerivAt (fun s => (g s * h s).toHomogeneous)
      (D * (h t).toHomogeneous + (g t).toHomogeneous * E) t := by
  simp only [toHomogeneous_mul]
  exact hg.mul hh

/-- MLS Proposition 2.14: spatial velocities compose with the first pose's adjoint. -/
theorem spatialVelocity_mul
    {g h : ℝ → RigidTransform} {D E : HomogeneousMatrix} {t : ℝ}
    (hg : HasDerivAt (fun s => (g s).toHomogeneous) D t)
    (hh : HasDerivAt (fun s => (h s).toHomogeneous) E t) :
    spatialVelocity (fun s => g s * h s)
        (D * (h t).toHomogeneous + (g t).toHomogeneous * E) t
        (hasDerivAt_toHomogeneous_mul hg hh) =
      spatialVelocity g D t hg + Twist.adjoint (g t) (spatialVelocity h E t hh) := by
  apply Twist.hat_injective
  rw [hat_spatialVelocity, Twist.hat_add, Twist.hat_adjoint,
    hat_spatialVelocity, hat_spatialVelocity]
  simp only [← toHomogeneous_inv]
  simp only [_root_.mul_inv_rev, toHomogeneous_mul, add_mul,
    mul_assoc, homogeneous_mul_inv_assoc]

/-- MLS Proposition 2.15: the body law uses the inverse of the second pose. -/
theorem bodyVelocity_mul
    {g h : ℝ → RigidTransform} {D E : HomogeneousMatrix} {t : ℝ}
    (hg : HasDerivAt (fun s => (g s).toHomogeneous) D t)
    (hh : HasDerivAt (fun s => (h s).toHomogeneous) E t) :
    bodyVelocity (fun s => g s * h s)
        (D * (h t).toHomogeneous + (g t).toHomogeneous * E) t
        (hasDerivAt_toHomogeneous_mul hg hh) =
      Twist.adjoint (h t)⁻¹ (bodyVelocity g D t hg) + bodyVelocity h E t hh := by
  apply Twist.hat_injective
  rw [hat_bodyVelocity, Twist.hat_add, Twist.hat_adjoint,
    hat_bodyVelocity, hat_bodyVelocity]
  simp only [← toHomogeneous_inv]
  simp only [_root_.mul_inv_rev, inv_inv, toHomogeneous_mul, mul_add,
    mul_assoc, homogeneous_inv_mul_assoc]

/-- A fixed left pose has zero derivative; only the moving curve contributes. -/
theorem hasDerivAt_toHomogeneous_const_mul
    (a : RigidTransform) {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}
    (hg : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    HasDerivAt (fun s => (a * g s).toHomogeneous) (a.toHomogeneous * D) t := by
  simp only [toHomogeneous_mul]
  exact hg.const_mul a.toHomogeneous

/-- MLS equation (2.62): a fixed change of spatial frame acts by the adjoint. -/
theorem spatialVelocity_const_mul
    (a : RigidTransform) {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}
    (hg : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    spatialVelocity (fun s => a * g s) (a.toHomogeneous * D) t
        (hasDerivAt_toHomogeneous_const_mul a hg) =
      Twist.adjoint a (spatialVelocity g D t hg) := by
  apply Twist.hat_injective
  rw [hat_spatialVelocity, Twist.hat_adjoint, hat_spatialVelocity]
  simp only [← toHomogeneous_inv]
  simp only [_root_.mul_inv_rev, toHomogeneous_mul, mul_assoc]

/-- MLS equation (2.63): body velocity is unchanged by a fixed spatial frame. -/
theorem bodyVelocity_const_mul
    (a : RigidTransform) {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}
    (hg : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    bodyVelocity (fun s => a * g s) (a.toHomogeneous * D) t
        (hasDerivAt_toHomogeneous_const_mul a hg) = bodyVelocity g D t hg := by
  apply Twist.hat_injective
  rw [hat_bodyVelocity, hat_bodyVelocity]
  simp only [← toHomogeneous_inv]
  simp only [_root_.mul_inv_rev, toHomogeneous_mul, mul_assoc,
    homogeneous_inv_mul_assoc]

/-- The inverse curve derivative follows from noncommutative matrix inversion
at the homogeneous unit; no separate inverse-curve differentiability is assumed. -/
theorem hasDerivAt_toHomogeneous_inv
    {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}
    (hg : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    HasDerivAt (fun s => ((g s)⁻¹).toHomogeneous)
      (-((g t)⁻¹.toHomogeneous * D * (g t)⁻¹.toHomogeneous)) t := by
  let U : HomogeneousMatrixˣ :=
    { val := (g t).toHomogeneous
      inv := ((g t)⁻¹).toHomogeneous
      val_inv := toHomogeneous_mul_inv (g t)
      inv_val := toHomogeneous_inv_mul (g t) }
  have hi : HasDerivAt (fun s => Ring.inverse ((g s).toHomogeneous))
      (-((g t)⁻¹.toHomogeneous * D * (g t)⁻¹.toHomogeneous)) t := by
    exact (hasFDerivAt_ringInverse (𝕜 := ℝ) U).comp_hasDerivAt t hg
  simpa only [← Matrix.nonsing_inv_eq_ringInverse, ← toHomogeneous_inv] using hi

/-- First identity of MLS Lemma 2.16: reversing frames exchanges body and
spatial velocities and changes the sign. -/
theorem bodyVelocity_eq_neg_spatialVelocity_inv
    {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}
    (hg : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    bodyVelocity g D t hg =
      -spatialVelocity (fun s => (g s)⁻¹)
        (-((g t)⁻¹.toHomogeneous * D * (g t)⁻¹.toHomogeneous)) t
        (hasDerivAt_toHomogeneous_inv hg) := by
  apply Twist.hat_injective
  rw [hat_bodyVelocity, Twist.hat_neg, hat_spatialVelocity]
  simp only [← toHomogeneous_inv, inv_inv, neg_mul, neg_neg, mul_assoc,
    toHomogeneous_inv_mul, mul_one]

/-- Second identity of MLS Lemma 2.16: the inverse-frame adjoint converts the
reversed body velocity before negation. -/
theorem bodyVelocity_eq_neg_adjoint_bodyVelocity_inv
    {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}
    (hg : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    bodyVelocity g D t hg =
      -Twist.adjoint (g t)⁻¹
        (bodyVelocity (fun s => (g s)⁻¹)
          (-((g t)⁻¹.toHomogeneous * D * (g t)⁻¹.toHomogeneous)) t
          (hasDerivAt_toHomogeneous_inv hg)) := by
  rw [bodyVelocity_eq_neg_spatialVelocity_inv hg,
    spatialVelocity_eq_adjoint_body (hasDerivAt_toHomogeneous_inv hg)]

end RigidTransform
end RoboLean
