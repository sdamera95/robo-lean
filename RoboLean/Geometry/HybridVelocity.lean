import RoboLean.Geometry.RigidVelocityComposition

/-!
# The hybrid representation of rigid-body velocity

MLS Exercise 18, pp. 78–79: the hybrid velocity `V^h_ab = (ṗ, ωˢ)` of a rigid motion `g(t) = (p(t),
R(t))` pairs the derivative of the origin of the body frame with the spatial angular velocity.
This file proves part (a), `V^h = diag(R, R) V^b`; part (b), the composition rule
`V^h_ac = Ad_{(-R_ab p_bc)} V^h_ab + Ad_{R_ab} V^h_bc`; and the change-of-frame formulas behind
parts (c) and (d): a fixed change of spatial frame `a` acts on `V^h` by `Ad_{R_a}` alone, and a
fixed change of body frame `b` acts by `Ad_{(-R p_b)}` alone.

Conventions: twists are `(v, ω)` with linear coordinates first and `Twist.adjoint` is (2.58),
p. 55; `Ad_p` is the adjoint of the pure translation `(p, I)` and `Ad_R` that of the pure rotation
`(0, R)`, as in part (b); velocities carry the derivative of the homogeneous pose matrix as in
`RigidTransform.spatialVelocity`. Part (e) (wrenches in hybrid coordinates) is not stated here.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean
namespace RigidTransform

variable {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}

/-- The hybrid velocity `V^h = (ṗ, ωˢ)` of MLS Exercise 18, p. 78: the derivative of the position
of the body-frame origin and the spatial angular velocity (2.48), with linear coordinates first.
The derivative `D` of the homogeneous pose matrix is carried as for `spatialVelocity`. -/
def hybridVelocity (g : ℝ → RigidTransform) (D : HomogeneousMatrix) (t : ℝ)
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) : Twist :=
  ⟨translationDerivative D, (spatialVelocity g D t h).angular⟩

/-- MLS Exercise 18(a), pp. 78–79: the hybrid velocity is the body velocity rotated by
`diag(R, R)`, `V^h = [[R, 0], [0, R]] V^b`, which is the adjoint of the pure rotation `(0, R)`
(equation (2.58), p. 55, with `p = 0`). -/
theorem hybridVelocity_eq_adjoint_bodyVelocity
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    hybridVelocity g D t h = Twist.adjoint ⟨(g t).rotation, 0⟩ (bodyVelocity g D t h) := by
  apply Twist.ext
  · simp [hybridVelocity, Twist.adjoint, Rotation.act_inv_act]
  · simp [hybridVelocity, Twist.adjoint, bodyVelocity_angular, Rotation.act_inv_act]

/-- The hybrid velocity of MLS Exercise 18, p. 78, is the spatial velocity (2.53), p. 54, moved to
the body-frame origin: `V^h = Ad_{(-p)} Vˢ`, the adjoint of the pure translation `(-p, I)`. -/
theorem hybridVelocity_eq_adjoint_spatialVelocity
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    hybridVelocity g D t h = Twist.adjoint ⟨1, -(g t).translation⟩ (spatialVelocity g D t h) := by
  apply Twist.ext
  · simp only [hybridVelocity, Twist.adjoint_linear, Rotation.act_one, spatialVelocity_linear,
      Vec3.neg_cross]
    rw [Vec3.cross_anticomm (g t).translation]
    abel
  · simp [hybridVelocity, Twist.adjoint]

/-- The spatial velocity (2.53), p. 54, recovered from the hybrid velocity of MLS Exercise 18,
p. 78: `Vˢ = Ad_p V^h`, the adjoint of the pure translation `(p, I)`. -/
theorem spatialVelocity_eq_adjoint_hybridVelocity
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    spatialVelocity g D t h = Twist.adjoint ⟨1, (g t).translation⟩ (hybridVelocity g D t h) := by
  rw [hybridVelocity_eq_adjoint_spatialVelocity, ← Twist.adjoint_mul]
  have : (⟨1, (g t).translation⟩ : RigidTransform) * ⟨1, -(g t).translation⟩ = 1 := by
    ext1 <;> simp
  rw [this, Twist.adjoint_one]

/-- MLS Exercise 18(b), p. 79: for `g_ac = g_ab g_bc`,
`V^h_ac = Ad_{(-R_ab p_bc)} V^h_ab + Ad_{R_ab} V^h_bc`, with `Ad_p` the adjoint of the pure
translation `(p, I)` and `Ad_R` that of the pure rotation `(0, R)`. -/
theorem hybridVelocity_mul {g k : ℝ → RigidTransform} {D E : HomogeneousMatrix} {t : ℝ}
    (hg : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t)
    (hk : HasDerivAt (fun s ↦ (k s).toHomogeneous) E t) :
    hybridVelocity (fun s ↦ g s * k s) (D * (k t).toHomogeneous + (g t).toHomogeneous * E) t
        (hasDerivAt_toHomogeneous_mul hg hk) =
      Twist.adjoint ⟨1, -(g t).rotation.act (k t).translation⟩ (hybridVelocity g D t hg) +
        Twist.adjoint ⟨(g t).rotation, 0⟩ (hybridVelocity k E t hk) := by
  rw [hybridVelocity_eq_adjoint_spatialVelocity, spatialVelocity_mul hg hk,
    spatialVelocity_eq_adjoint_hybridVelocity hg, spatialVelocity_eq_adjoint_hybridVelocity hk,
    Twist.adjoint_add, ← Twist.adjoint_mul, ← Twist.adjoint_mul, ← Twist.adjoint_mul]
  congr 2
  · ext1 <;> simp [add_comm]
  · ext1 <;> simp

/-- MLS Exercise 18(c), p. 79: a fixed change of spatial frame `a` acts on the hybrid velocity by
the pure rotation `Ad_{R_a}` alone; the position of the spatial frame does not enter. -/
theorem hybridVelocity_const_mul (a : RigidTransform)
    (hg : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    hybridVelocity (fun s ↦ a * g s) (a.toHomogeneous * D) t
        (hasDerivAt_toHomogeneous_const_mul a hg) =
      Twist.adjoint ⟨a.rotation, 0⟩ (hybridVelocity g D t hg) := by
  rw [hybridVelocity_eq_adjoint_spatialVelocity, spatialVelocity_const_mul a hg,
    spatialVelocity_eq_adjoint_hybridVelocity hg, ← Twist.adjoint_mul, ← Twist.adjoint_mul]
  congr 1
  ext1 <;> simp

/-- MLS Exercise 18(c), p. 79, first half: the hybrid velocity is independent of the position of
the spatial frame: a fixed spatial change `a` with rotation `I` leaves it unchanged. -/
theorem hybridVelocity_const_mul_of_rotation_eq_one (a : RigidTransform) (ha : a.rotation = 1)
    (hg : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    hybridVelocity (fun s ↦ a * g s) (a.toHomogeneous * D) t
        (hasDerivAt_toHomogeneous_const_mul a hg) = hybridVelocity g D t hg := by
  rw [hybridVelocity_const_mul, ha]
  exact Twist.adjoint_one _

/-- A fixed right pose has zero derivative; only the moving curve contributes (supporting lemma for
MLS Exercise 18(d), p. 79, a fixed change of body frame). -/
theorem hasDerivAt_toHomogeneous_mul_const (b : RigidTransform)
    (hg : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    HasDerivAt (fun s ↦ (g s * b).toHomogeneous) (D * b.toHomogeneous) t := by
  simp only [toHomogeneous_mul]
  exact hg.mul_const b.toHomogeneous

/-- MLS Exercise 18(d), p. 79: a fixed change of body frame `b` acts on the hybrid velocity by the
pure translation `Ad_{(-R p_b)}` alone, with `R` the current orientation; the orientation of the
body frame does not enter. -/
theorem hybridVelocity_mul_const (b : RigidTransform)
    (hg : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    hybridVelocity (fun s ↦ g s * b) (D * b.toHomogeneous) t
        (hasDerivAt_toHomogeneous_mul_const b hg) =
      Twist.adjoint ⟨1, -(g t).rotation.act b.translation⟩ (hybridVelocity g D t hg) := by
  have hs : spatialVelocity (fun s ↦ g s * b) (D * b.toHomogeneous) t
      (hasDerivAt_toHomogeneous_mul_const b hg) = spatialVelocity g D t hg := by
    apply Twist.hat_injective
    rw [hat_spatialVelocity, hat_spatialVelocity]
    simp only [← toHomogeneous_inv]
    simp only [_root_.mul_inv_rev, toHomogeneous_mul, mul_assoc]
    rw [← mul_assoc b.toHomogeneous, toHomogeneous_mul_inv, one_mul]
  rw [hybridVelocity_eq_adjoint_spatialVelocity, hs, spatialVelocity_eq_adjoint_hybridVelocity hg,
    ← Twist.adjoint_mul]
  congr 1
  ext1 <;> simp [add_comm]

/-- MLS Exercise 18(d), p. 79, first half: the hybrid velocity is independent of the orientation of
the body frame: a fixed body change `b` with translation `0` leaves it unchanged. -/
theorem hybridVelocity_mul_const_of_translation_eq_zero (b : RigidTransform)
    (hb : b.translation = 0) (hg : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    hybridVelocity (fun s ↦ g s * b) (D * b.toHomogeneous) t
        (hasDerivAt_toHomogeneous_mul_const b hg) = hybridVelocity g D t hg := by
  rw [hybridVelocity_mul_const, hb, map_zero, neg_zero]
  exact Twist.adjoint_one _

end RigidTransform
end RoboLean
