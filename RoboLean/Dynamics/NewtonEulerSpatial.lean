import RoboLean.Dynamics.NewtonEuler
import RoboLean.Control.MatrixAnalysis

/-!
# Euler's equation in spatial coordinates and the derivation of (4.14)–(4.16)

MLS Chapter 4, §2.4, printed pp. 165–167, and Exercise 4 of p. 208.

**What MLS states.** For a body frame at the mass center with configuration `g = (p, R)`, Newton's
law (4.12) `f = m p̈` (as `f = d/dt (m ṗ)`, p. 166) and Euler's equation (4.13)
`I′ ω̇ˢ + ωˢ × I′ ωˢ = τ` with `I′ = R I Rᵀ` (p. 166), obtained by expanding `τ = d/dt (I′ ωˢ)`;
"we rewrite Newton's equation using the body velocity `vᵇ = Rᵀ ṗ` and body force `fᵇ = Rᵀ f`", giving
(4.14) `m v̇ᵇ + ωᵇ × m vᵇ = fᵇ`; with `ωᵇ = Rᵀ ωˢ` and `τᵇ = Rᵀ τ` "a straightforward computation
shows" (4.15) `I ω̇ᵇ + ωᵇ × I ωᵇ = τᵇ`; together (4.16), the Newton–Euler equation in body
coordinates (p. 167). Exercise 4 (pp. 208–209): "Show that Euler's equation written in spatial
coordinates is given by `I′ ω̇ˢ + ωˢ × I′ ωˢ = τ`, where `I′ = R I Rᵀ`".

**Formalized (derived, not defined).**

* `spatialInertia R 𝓘 = R 𝓘 Rᵀ` (`I′`, p. 166) and `I′ ωˢ = R (𝓘 (Rᵀ ωˢ))`.
* The product rule for a rotating vector, `d/dt (R v) = ωˢ × R v + R v̇` (`hasDerivAt_act_curve`),
  and `ω̇ᵇ = Rᵀ ω̇ˢ` for `ωᵇ = Rᵀ ωˢ` (`hasDerivAt_inv_act_angular`), from the library's
  `Rotation.spatialAngularVelocity` with actual derivative data.
* The expansion of p. 166: `d/dt (I′ ωˢ) = I′ ω̇ˢ + ωˢ × I′ ωˢ`, the term `I′ (R Ṙᵀ ωˢ)` being zero
  (`hasDerivAt_spatialAngularMomentum`); hence (4.13), Exercise 4: `τ = d/dt (I′ ωˢ)` exactly when
  `I′ ω̇ˢ + ωˢ × I′ ωˢ = τ` (`euler_spatial_iff`).
* (4.15) from (4.13): at one instant, `𝓘 (Rᵀ ω̇ˢ) + ωᵇ × 𝓘 ωᵇ = Rᵀ τ` exactly when (4.13) holds
  (`euler_body_iff_euler_spatial`).
* (4.14) from (4.12): `f = d/dt (m ṗ)` exactly when `m v̇ᵇ + ωᵇ × m vᵇ = Rᵀ f`, for `vᵇ = Rᵀ ṗ` with
  an actual derivative `v̇ᵇ` (`newton_iff_newton_body`).
* (4.16) from (4.12)–(4.13) for a pose curve with the library's `RigidTransform.bodyVelocity`
  supplying `Vᵇ`: Newton's and Euler's laws in the inertial frame hold at `t` exactly when
  `NewtonEulerEquation` holds with the body acceleration `(v̇ᵇ, Rᵀ ω̇ˢ)`, which is the actual
  derivative of `Vᵇ` (`newtonEuler_iff_inertial`, `hasDerivAt_bodyVelocityCurve_angular`).

Conventions: twists `(v, ω)`, wrenches `(f, τ)`; `f` and `τ` are applied at the mass center with
coordinates in the inertial frame, `fᵇ = Rᵀ f`, `τᵇ = Rᵀ τ`; the inertia tensor `𝓘` is any real
`3 × 3` matrix (its symmetry is not needed here). Derivatives are actual derivative data at one
instant. Nothing here asserts anything about a physical body.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean
namespace RigidBody

/-- **The instantaneous inertia tensor relative to the inertial frame, `I′ = R I Rᵀ` (MLS printed
p. 166 and Exercise 4, pp. 208–209).** -/
def spatialInertia (R : Rotation) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  R.val * 𝓘 * R.valᵀ

/-- **`I′ ωˢ = R (I (Rᵀ ωˢ))` (MLS printed p. 166).** -/
theorem inertiaAct_spatialInertia (R : Rotation) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (ω : Vec3) :
    inertiaAct (spatialInertia R 𝓘) ω = R.act (inertiaAct 𝓘 (R⁻¹.act ω)) := by
  apply WithLp.ofLp_injective
  change (R.val * 𝓘 * R.valᵀ) *ᵥ WithLp.ofLp ω = R.val *ᵥ (𝓘 *ᵥ (R.valᵀ *ᵥ WithLp.ofLp ω))
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

private theorem act_eq_toLp (R : Rotation) (v : Vec3) :
    R.act v = WithLp.toLp 2 (R.val *ᵥ WithLp.ofLp v) := rfl

/-- **The product rule for a rotating vector (MLS printed p. 166, the expansion of
`d/dt (R I Rᵀ ωˢ)`, with (2.47)):** for a rotation curve with derivative `A` at `t` and a vector
curve `v` with derivative `v'` at `t`, `d/dt (R v) = ωˢ × R v + R v'`, `ωˢ` the spatial angular
velocity (MLS (2.48)). -/
theorem hasDerivAt_act_curve {R : ℝ → Rotation} {A : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hR : HasDerivAt (fun s => (R s).val) A t) {v : ℝ → Vec3} {v' : Vec3}
    (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => (R s).act (v s))
      (Vec3.cross (Rotation.spatialAngularVelocity R A t hR) ((R t).act (v t)) + (R t).act v') t := by
  have hRe := Control.hasDerivAt_matrix_iff.mp hR
  have hv1 : HasDerivAt (fun s => WithLp.ofLp (v s)) (WithLp.ofLp v') t :=
    (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hv
  have h1 := Control.hasDerivAt_matrix_mulVec_rect hRe hv1
  have h2 : HasDerivAt (fun s => (WithLp.toLp 2 ((R s).val *ᵥ WithLp.ofLp (v s)) : Vec3))
      (WithLp.toLp 2 (A *ᵥ WithLp.ofLp (v t) + (R t).val *ᵥ WithLp.ofLp v')) t :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h1
  have e : (WithLp.toLp 2 (A *ᵥ WithLp.ofLp (v t) + (R t).val *ᵥ WithLp.ofLp v') : Vec3) =
      Vec3.cross (Rotation.spatialAngularVelocity R A t hR) ((R t).act (v t)) + (R t).act v' := by
    rw [← Rotation.spatial_velocity_eq_cross hR (v t)]
    rfl
  rw [← e]
  exact h2

/-- **`ω̇ᵇ = Rᵀ ω̇ˢ` (MLS printed p. 167, "Euler's equation in terms of the body angular velocity
`ωᵇ = Rᵀ ωˢ`"):** if `ω` is a curve with `ω(t)` the spatial angular velocity of `R` at `t` and
derivative `ω'` at `t`, then `s ↦ R(s)ᵀ ω(s)` has derivative `R(t)ᵀ ω'` at `t` (the term
`Ṙᵀ ωˢ = −Rᵀ (ωˢ × ωˢ)` vanishes). -/
theorem hasDerivAt_inv_act_angular {R : ℝ → Rotation} {A : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hR : HasDerivAt (fun s => (R s).val) A t) {ω : ℝ → Vec3} {ω' : Vec3}
    (hω0 : ω t = Rotation.spatialAngularVelocity R A t hR) (hω : HasDerivAt ω ω' t) :
    HasDerivAt (fun s => (R s)⁻¹.act (ω s)) ((R t)⁻¹.act ω') t := by
  have hRt : HasDerivAt (fun s => ((R s)⁻¹).val) Aᵀ t := Rotation.hasDerivAt_val_transpose hR
  have hRe := Control.hasDerivAt_matrix_iff.mp hRt
  have hv1 : HasDerivAt (fun s => WithLp.ofLp (ω s)) (WithLp.ofLp ω') t :=
    (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hω
  have h1 := Control.hasDerivAt_matrix_mulVec_rect hRe hv1
  have h2 : HasDerivAt (fun s => (WithLp.toLp 2 (((R s)⁻¹).val *ᵥ WithLp.ofLp (ω s)) : Vec3))
      (WithLp.toLp 2 (Aᵀ *ᵥ WithLp.ofLp (ω t) + ((R t)⁻¹).val *ᵥ WithLp.ofLp ω')) t :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h1
  have hA : A = Vec3.hat (Rotation.spatialAngularVelocity R A t hR) * (R t).val := by
    rw [Rotation.hat_spatialAngularVelocity, Matrix.mul_assoc, Rotation.transpose_mul,
      Matrix.mul_one]
  have hz : Aᵀ *ᵥ WithLp.ofLp (ω t) = 0 := by
    rw [hA, hω0, Matrix.transpose_mul, Vec3.hat_transpose, ← Matrix.mulVec_mulVec,
      Matrix.neg_mulVec, Vec3.hat_mulVec_self, neg_zero, Matrix.mulVec_zero]
  rw [hz, zero_add] at h2
  exact h2

/-- **The expansion of MLS printed p. 166:** `d/dt (I′ ωˢ) = I′ ω̇ˢ + ωˢ × I′ ωˢ` with
`I′ = R I Rᵀ`, for a rotation curve with derivative `A` at `t` and a curve `ω` equal to the spatial
angular velocity at `t` with derivative `ω'` at `t` ("the last term of this equation is zero"). -/
theorem hasDerivAt_spatialAngularMomentum {R : ℝ → Rotation} {A : Matrix (Fin 3) (Fin 3) ℝ}
    {t : ℝ} (hR : HasDerivAt (fun s => (R s).val) A t) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ)
    {ω : ℝ → Vec3} {ω' : Vec3} (hω0 : ω t = Rotation.spatialAngularVelocity R A t hR)
    (hω : HasDerivAt ω ω' t) :
    HasDerivAt (fun s => inertiaAct (spatialInertia (R s) 𝓘) (ω s))
      (inertiaAct (spatialInertia (R t) 𝓘) ω' +
        Vec3.cross (ω t) (inertiaAct (spatialInertia (R t) 𝓘) (ω t))) t := by
  have hb := hasDerivAt_inv_act_angular hR hω0 hω
  let L : Vec3 →L[ℝ] Vec3 := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin 𝓘)
  have hL : ∀ x, L x = inertiaAct 𝓘 x := fun x => rfl
  have hI : HasDerivAt (fun s => inertiaAct 𝓘 ((R s)⁻¹.act (ω s)))
      (inertiaAct 𝓘 ((R t)⁻¹.act ω')) t := by
    have := L.hasFDerivAt.comp_hasDerivAt t hb
    simpa only [Function.comp_def, hL] using this
  have h := hasDerivAt_act_curve hR hI
  simp only [← inertiaAct_spatialInertia, ← hω0] at h
  rw [add_comm]
  exact h

/-- **MLS eq. (4.13), p. 166, and Exercise 4, pp. 208–209: Euler's equation in spatial
coordinates.** For a rotation curve with derivative `A` at `t` and a curve `ω` equal to the spatial
angular velocity at `t` with derivative `ω'`, the torque `τ` (inertial coordinates, at the mass
center) equals the rate of the angular momentum, `τ = d/dt (I′ ωˢ)`, exactly when
`I′ ω̇ˢ + ωˢ × I′ ωˢ = τ` with `I′ = R I Rᵀ`. -/
theorem euler_spatial_iff {R : ℝ → Rotation} {A : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hR : HasDerivAt (fun s => (R s).val) A t) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) {ω : ℝ → Vec3}
    {ω' : Vec3} (hω0 : ω t = Rotation.spatialAngularVelocity R A t hR) (hω : HasDerivAt ω ω' t)
    (τ : Vec3) :
    HasDerivAt (fun s => inertiaAct (spatialInertia (R s) 𝓘) (ω s)) τ t ↔
      inertiaAct (spatialInertia (R t) 𝓘) ω' +
        Vec3.cross (ω t) (inertiaAct (spatialInertia (R t) 𝓘) (ω t)) = τ := by
  have h := hasDerivAt_spatialAngularMomentum hR 𝓘 hω0 hω
  constructor
  · intro hτ
    exact h.unique hτ
  · intro he
    rw [← he]
    exact h

/-- **MLS eq. (4.15) from (4.13), p. 167 ("a straightforward computation shows"), at one
instant:** with `ωᵇ = Rᵀ ωˢ`, `ω̇ᵇ = Rᵀ ω̇ˢ` and `τᵇ = Rᵀ τ`, Euler's equation in body coordinates
`I ω̇ᵇ + ωᵇ × I ωᵇ = τᵇ` holds exactly when Euler's equation in spatial coordinates
`I′ ω̇ˢ + ωˢ × I′ ωˢ = τ` does (`I′ = R I Rᵀ`). -/
theorem euler_body_iff_euler_spatial (R : Rotation) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ)
    (ω ω' τ : Vec3) :
    inertiaAct 𝓘 (R⁻¹.act ω') + Vec3.cross (R⁻¹.act ω) (inertiaAct 𝓘 (R⁻¹.act ω)) = R⁻¹.act τ ↔
      inertiaAct (spatialInertia R 𝓘) ω' +
        Vec3.cross ω (inertiaAct (spatialInertia R 𝓘) ω) = τ := by
  have e : inertiaAct (spatialInertia R 𝓘) ω' + Vec3.cross ω (inertiaAct (spatialInertia R 𝓘) ω) =
      R.act (inertiaAct 𝓘 (R⁻¹.act ω') +
        Vec3.cross (R⁻¹.act ω) (inertiaAct 𝓘 (R⁻¹.act ω))) := by
    rw [map_add, Rotation.act_cross, Rotation.act_inv_act, inertiaAct_spatialInertia,
      inertiaAct_spatialInertia]
  rw [e]
  constructor
  · intro h
    rw [h, Rotation.act_inv_act]
  · intro h
    rw [← h, Rotation.inv_act_act]

/-- **MLS eq. (4.14) from (4.12), p. 167: Newton's law in body coordinates.** For a rotation curve
with derivative `A` at `t`, a velocity curve `ṗ` of the mass center (inertial coordinates) whose
body coordinates `vᵇ = Rᵀ ṗ` have the derivative `v̇ᵇ` at `t`, and a force `f` (inertial
coordinates, at the mass center): `f = d/dt (m ṗ)` exactly when `m v̇ᵇ + ωᵇ × m vᵇ = Rᵀ f`, with
`ωᵇ` the body angular velocity (MLS (2.49)). -/
theorem newton_iff_newton_body {R : ℝ → Rotation} {A : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hR : HasDerivAt (fun s => (R s).val) A t) (m : ℝ) {pd : ℝ → Vec3} {vbd : Vec3}
    (hvb : HasDerivAt (fun s => (R s)⁻¹.act (pd s)) vbd t) (f : Vec3) :
    HasDerivAt (fun s => m • pd s) f t ↔
      m • vbd + Vec3.cross (Rotation.bodyAngularVelocity R A t hR) (m • (R t)⁻¹.act (pd t)) =
        (R t)⁻¹.act f := by
  have h1 := (hasDerivAt_act_curve hR hvb).const_smul m
  simp only [Rotation.act_inv_act] at h1
  have e : m • (Vec3.cross (Rotation.spatialAngularVelocity R A t hR) (pd t) + (R t).act vbd) =
      (R t).act (m • vbd + Vec3.cross (Rotation.bodyAngularVelocity R A t hR)
        (m • (R t)⁻¹.act (pd t))) := by
    rw [map_add, map_smul, Rotation.act_cross, Rotation.bodyAngularVelocity_eq hR,
      Rotation.act_inv_act, map_smul, Rotation.act_inv_act, Vec3.cross_smul, smul_add]
    abel
  rw [e] at h1
  constructor
  · intro hf
    rw [← h1.unique hf, Rotation.inv_act_act]
  · intro he
    rw [← Rotation.act_inv_act (R t) f, ← he]
    exact h1

/-- **`ω̇ᵇ = Rᵀ ω̇ˢ` along a pose curve (MLS printed p. 167), with the library's body velocity
`RigidTransform.bodyVelocity` (MLS (2.55)) supplying `Vᵇ`:** if the spatial angular velocity of a
pose curve with derivative data `D` has the derivative `ω'` at `t`, the angular part of the body
velocity curve has the derivative `R(t)ᵀ ω'` at `t`. -/
theorem hasDerivAt_bodyVelocityCurve_angular {g : ℝ → RigidTransform} {D : ℝ → HomogeneousMatrix}
    (hD : ∀ s, HasDerivAt (fun r => (g r).toHomogeneous) (D s) s) {t : ℝ} {ω' : Vec3}
    (hω : HasDerivAt (fun s => (RigidTransform.spatialVelocity g (D s) s (hD s)).angular) ω' t) :
    HasDerivAt (fun s => (bodyVelocityCurve g D hD s).angular) ((g t).rotation⁻¹.act ω') t := by
  have e : (fun s => (bodyVelocityCurve g D hD s).angular) =
      fun s => (g s).rotation⁻¹.act (RigidTransform.spatialVelocity g (D s) s (hD s)).angular := by
    funext s
    exact RigidTransform.bodyVelocity_angular (hD s)
  rw [e]
  exact hasDerivAt_inv_act_angular (RigidTransform.hasDerivAt_rotation (hD t)) rfl hω

/-- **MLS eq. (4.16) derived from (4.12)–(4.13), pp. 166–167: the Newton–Euler equation in body
coordinates.** For a pose curve `g = (p, R)` of the mass-center frame with derivative data `D` at
every time, its body velocity curve `Vᵇ` (the library's `RigidTransform.bodyVelocity`, MLS (2.55)),
an actual derivative `a` of `vᵇ = Rᵀ ṗ` at `t` and an actual derivative `ω'` of the spatial angular
velocity `ωˢ` at `t`: Newton's law `f = d/dt (m ṗ)` (4.12) and Euler's law `τ = d/dt (I′ ωˢ)`
(whose expansion is (4.13)), with `f`, `τ` at the mass center in inertial coordinates, hold at `t`
exactly when (4.16) holds with the body acceleration `(a, Rᵀ ω')` and the body wrench
`Fᵇ = (Rᵀ f, Rᵀ τ)`. Twist order `(v, ω)`, wrench order `(f, τ)`. -/
theorem newtonEuler_iff_inertial {g : ℝ → RigidTransform} {D : ℝ → HomogeneousMatrix}
    (hD : ∀ s, HasDerivAt (fun r => (g r).toHomogeneous) (D s) s) (m : ℝ)
    (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) {t : ℝ} {a ω' : Vec3}
    (hv : HasDerivAt (fun s => (bodyVelocityCurve g D hD s).linear) a t)
    (hω : HasDerivAt (fun s => (RigidTransform.spatialVelocity g (D s) s (hD s)).angular) ω' t)
    (f τ : Vec3) :
    (HasDerivAt (fun s => m • RigidTransform.translationDerivative (D s)) f t ∧
        HasDerivAt (fun s => inertiaAct (spatialInertia (g s).rotation 𝓘)
          (RigidTransform.spatialVelocity g (D s) s (hD s)).angular) τ t) ↔
      NewtonEulerEquation m 𝓘 (bodyVelocityCurve g D hD t) ⟨a, (g t).rotation⁻¹.act ω'⟩
        ⟨(g t).rotation⁻¹.act f, (g t).rotation⁻¹.act τ⟩ := by
  have hR := RigidTransform.hasDerivAt_rotation (hD t)
  rw [newtonEulerEquation_iff]
  refine and_congr (newton_iff_newton_body hR m hv f) ?_
  rw [euler_spatial_iff hR 𝓘 rfl hω τ, ← euler_body_iff_euler_spatial]
  have hb : (bodyVelocityCurve g D hD t).angular =
      (g t).rotation⁻¹.act (RigidTransform.spatialVelocity g (D t) t (hD t)).angular :=
    RigidTransform.bodyVelocity_angular (hD t)
  rw [hb]

end RigidBody
end RoboLean
