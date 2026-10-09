import RoboLean.Geometry.Wrench
import RoboLean.Geometry.RigidVelocity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Point-force power and interval work

MLS printed pp. 61–63 defines wrench/twist power and its time integral (X48).
The coordinate moment of a force applied at a point is proved to pair with
rigid velocity as force dotted with the actual point-trajectory derivative.
Work below requires interval integrability, and pose-derived formulas carry
actual homogeneous derivative evidence. Integrals are oriented real intervals.

Frame labels, torque origins, and compatible physical units remain conventions.
These exact-real identities do not certify force measurements, contact models,
energy balance of a particular robot, or a numerical integration procedure.
-/

noncomputable section

open Matrix MeasureTheory

namespace RoboLean
namespace Wrench

/-- A force applied at `q`, represented about the coordinate-frame origin. -/
def pointForce (q f : Vec3) : Wrench := (f, Vec3.cross q f)

@[simp] theorem pointForce_force (q f : Vec3) : (pointForce q f).force = f := rfl
@[simp] theorem pointForce_torque (q f : Vec3) :
    (pointForce q f).torque = Vec3.cross q f := rfl

private theorem inner_cross_power (q f ω : Vec3) :
    inner ℝ (Vec3.cross q f) ω = inner ℝ f (Vec3.cross ω q) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change WithLp.ofLp ω ⬝ᵥ crossProduct (WithLp.ofLp q) (WithLp.ofLp f) =
    crossProduct (WithLp.ofLp ω) (WithLp.ofLp q) ⬝ᵥ WithLp.ofLp f
  exact (triple_product_permutation (WithLp.ofLp f) (WithLp.ofLp ω)
    (WithLp.ofLp q)).symm.trans (dotProduct_comm _ _)

/-- The moment-origin term converts wrench power into force dotted with the
rigid velocity of its application point. -/
theorem pair_pointForce (q f : Vec3) (ξ : Twist) :
    pair (pointForce q f) ξ = inner ℝ f (Vec3.cross ξ.angular q + ξ.linear) := by
  simp only [pair, pointForce_force, pointForce_torque, inner_add_right]
  rw [inner_cross_power]
  exact add_comm _ _

/-- Point force transfer includes both coordinate rotation and change of moment origin. -/
theorem transform_pointForce (g : RigidTransform) (q f : Vec3) :
    transform g (pointForce q f) = pointForce (g.applyPoint q) (g.applyVector f) := by
  apply Prod.ext
  · rfl
  · change Vec3.cross g.translation (g.rotation.act f) + g.rotation.act (Vec3.cross q f) =
      Vec3.cross (g.rotation.act q + g.translation) (g.rotation.act f)
    rw [Rotation.act_cross, Vec3.add_cross]
    exact add_comm _ _

/-- A point fixed in the body has an actual derivative; its point-force power
is force dotted with that derivative, rather than an assumed velocity symbol. -/
theorem power_pointForce_eq_force_dot_deriv
    {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}
    (h : HasDerivAt (fun s => (g s).toHomogeneous) D t) (q f : Vec3) :
    pair (pointForce ((g t).applyPoint q) f) (RigidTransform.spatialVelocity g D t h) =
      inner ℝ f (deriv (fun s => (g s).applyPoint q) t) := by
  rw [pair_pointForce, (RigidTransform.hasDerivAt_applyPoint_spatial h q).deriv]

/-- Actual spatial/body velocity correspondence preserves the pairing with the
compatibly transferred wrench at the same time. -/
theorem power_spatial_eq_body
    {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}
    (h : HasDerivAt (fun s => (g s).toHomogeneous) D t) (F : Wrench) :
    pair (transform (g t) F) (RigidTransform.spatialVelocity g D t h) =
      pair F (RigidTransform.bodyVelocity g D t h) := by
  rw [RigidTransform.spatialVelocity_eq_adjoint_body h, pair_transform_adjoint]

/-- MLS p. 61 interval work, restricted to integrable instantaneous power. -/
def intervalWork (F : ℝ → Wrench) (V : ℝ → Twist) (a b : ℝ)
    (_h : IntervalIntegrable (fun t => pair (F t) (V t)) volume a b) : ℝ :=
  ∫ t in a..b, pair (F t) (V t)

/-- A compatible pointwise frame conversion preserves the actual interval integral.
No claim is made that an arbitrary transformed `V` is a pose derivative. -/
theorem intervalWork_transform (g : ℝ → RigidTransform) (F : ℝ → Wrench)
    (V : ℝ → Twist) (a b : ℝ)
    (h : IntervalIntegrable (fun t => pair (F t) (V t)) volume a b) :
    intervalWork (fun t => transform (g t) (F t)) (fun t => Twist.adjoint (g t) (V t)) a b
        (by simpa only [pair_transform_adjoint] using h) = intervalWork F V a b h := by
  unfold intervalWork
  apply intervalIntegral.integral_congr
  intro t _
  exact pair_transform_adjoint (g t) (F t) (V t)

/-- Spatial and body work integrals agree for the supplied actual pose trajectory. -/
theorem intervalWork_spatial_eq_body (g : ℝ → RigidTransform) (D : ℝ → HomogeneousMatrix)
    (h : ∀ t, HasDerivAt (fun s => (g s).toHomogeneous) (D t) t)
    (F : ℝ → Wrench) (a b : ℝ)
    (hw : IntervalIntegrable
      (fun t => pair (F t) (RigidTransform.bodyVelocity g (D t) t (h t))) volume a b) :
    intervalWork (fun t => transform (g t) (F t))
        (fun t => RigidTransform.spatialVelocity g (D t) t (h t)) a b
        (by simpa only [power_spatial_eq_body] using hw) =
      intervalWork F (fun t => RigidTransform.bodyVelocity g (D t) t (h t)) a b hw := by
  unfold intervalWork
  apply intervalIntegral.integral_congr
  intro t _
  exact power_spatial_eq_body (h t) (F t)

/-- Point-force pairing is integrable exactly when force dotted with the actual
point velocity is integrable, for the supplied differentiable pose curve. -/
theorem intervalIntegrable_pointForce_iff (g : ℝ → RigidTransform) (D : ℝ → HomogeneousMatrix)
    (h : ∀ t, HasDerivAt (fun s => (g s).toHomogeneous) (D t) t)
    (q : Vec3) (f : ℝ → Vec3) (a b : ℝ) :
    IntervalIntegrable
        (fun t => pair (pointForce ((g t).applyPoint q) (f t))
          (RigidTransform.spatialVelocity g (D t) t (h t))) volume a b ↔
      IntervalIntegrable (fun t => inner ℝ (f t) (deriv (fun s => (g s).applyPoint q) t))
        volume a b := by
  apply intervalIntegrable_congr
  intro t _
  exact power_pointForce_eq_force_dot_deriv (h t) q (f t)

/-- Interval wrench work of a force at a body-fixed point equals the integral
of force dotted with that point's actual spatial velocity. -/
theorem intervalWork_pointForce (g : ℝ → RigidTransform) (D : ℝ → HomogeneousMatrix)
    (h : ∀ t, HasDerivAt (fun s => (g s).toHomogeneous) (D t) t)
    (q : Vec3) (f : ℝ → Vec3) (a b : ℝ)
    (hw : IntervalIntegrable
      (fun t => inner ℝ (f t) (deriv (fun s => (g s).applyPoint q) t)) volume a b) :
    intervalWork (fun t => pointForce ((g t).applyPoint q) (f t))
        (fun t => RigidTransform.spatialVelocity g (D t) t (h t)) a b
        ((intervalIntegrable_pointForce_iff g D h q f a b).mpr hw) =
      ∫ t in a..b, inner ℝ (f t) (deriv (fun s => (g s).applyPoint q) t) := by
  unfold intervalWork
  apply intervalIntegral.integral_congr
  intro t _
  exact power_pointForce_eq_force_dot_deriv (h t) q (f t)

/-- Adding wrenches in one common frame adds their integrable interval work. -/
theorem intervalWork_add (F G : ℝ → Wrench) (V : ℝ → Twist) (a b : ℝ)
    (hF : IntervalIntegrable (fun t => pair (F t) (V t)) volume a b)
    (hG : IntervalIntegrable (fun t => pair (G t) (V t)) volume a b) :
    intervalWork (fun t => F t + G t) V a b
        (by simpa only [pair_add_left] using hF.add hG) =
      intervalWork F V a b hF + intervalWork G V a b hG := by
  simp only [intervalWork, pair_add_left]
  exact intervalIntegral.integral_add hF hG

end Wrench
end RoboLean
