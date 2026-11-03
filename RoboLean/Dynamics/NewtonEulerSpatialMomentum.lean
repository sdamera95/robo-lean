import RoboLean.Dynamics.NewtonEulerSpatial

/-!
# The Newton–Euler equations in spatial coordinates: Chapter 4 Exercise 5

MLS Chapter 4, Exercise 5, printed p. 209: "Calculate the Newton-Euler equations in spatial
coordinates." Page 167: "It is also possible to write the Newton-Euler equations relative to a
spatial coordinate frame ... the equations for linear and angular motion are coupled, so that the
translational motion still depends on the rotational motion."

**Formalized (one reading of an open-ended exercise).** In the inertial frame, with the mass center
at `p`, the spatial momentum is the pair `(m ṗ, I′ ωˢ + p × m ṗ)`, the linear momentum and the
angular momentum about the origin of the inertial frame, and the wrench applied at the mass center
moved to the origin is `(f, τ + p × f)`. Its balance, `d/dt (m ṗ) = f` and
`d/dt (I′ ωˢ + p × m ṗ) = τ + p × f`, holds exactly when Newton's law (4.12) and Euler's equation
in spatial coordinates (4.13) hold (`newtonEuler_spatial_iff`). The second balance involves `p` and
`ṗ`, the coupling the book mentions; it reduces to (4.13) by `ṗ × m ṗ = 0` and (4.12). The product
rule for the cross product of two curves is `Vec3.hasDerivAt_cross`.

Conventions: `f`, `τ` applied at the mass center with inertial coordinates; `ωˢ` the spatial
angular velocity of the library; `I′ = R 𝓘 Rᵀ`. The matrix form `𝓜ˢ V̇ˢ + … = Fˢ` in spatial twist
coordinates is not stated. Nothing here asserts anything about a physical body.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean

namespace Vec3

/-- **The product rule for the cross product of two curves (MLS printed p. 166, used in the
expansion of `d/dt (I′ ωˢ)`, and p. 26 for the bilinearity of `×`):**
`d/dt (u × v) = u̇ × v + u × v̇`. -/
theorem hasDerivAt_cross {u v : ℝ → Vec3} {u' v' : Vec3} {t : ℝ} (hu : HasDerivAt u u' t)
    (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => cross (u s) (v s)) (cross u' (v t) + cross (u t) v') t := by
  have hU : ∀ i, HasDerivAt (fun s => (u s).ofLp i) (u'.ofLp i) t := fun i =>
    hasDerivAt_pi.mp
      ((EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hu) i
  have hV : ∀ i, HasDerivAt (fun s => (v s).ofLp i) (v'.ofLp i) t := fun i =>
    hasDerivAt_pi.mp
      ((EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hv) i
  have h : HasDerivAt (fun s => crossProduct (WithLp.ofLp (u s)) (WithLp.ofLp (v s)))
      (crossProduct (WithLp.ofLp u') (WithLp.ofLp (v t)) +
        crossProduct (WithLp.ofLp (u t)) (WithLp.ofLp v')) t := by
    refine hasDerivAt_pi.mpr fun k => ?_
    fin_cases k
    · convert ((hU 1).mul (hV 2)).sub ((hU 2).mul (hV 1)) using 1
      · funext s
        simp [cross_apply]
      · simp [cross_apply]
        ring
    · convert ((hU 2).mul (hV 0)).sub ((hU 0).mul (hV 2)) using 1
      · funext s
        simp [cross_apply]
      · simp [cross_apply]
        ring
    · convert ((hU 0).mul (hV 1)).sub ((hU 1).mul (hV 0)) using 1
      · funext s
        simp [cross_apply]
      · simp [cross_apply]
        ring
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h

private theorem cross_self' (u : Vec3) : cross u u = 0 := by
  apply WithLp.ofLp_injective
  simp [cross_coordinates]

end Vec3

namespace RigidBody

/-- **MLS Chapter 4, Exercise 5, p. 209: the Newton–Euler equations in spatial coordinates.** For
a rotation curve with derivative `A` at `t`, a curve `ω` equal to the spatial angular velocity at
`t` with derivative `ω'`, the mass center `p` with velocity `ṗ(t)` at `t`, and `f`, `τ` applied at
the mass center in inertial coordinates: the spatial momentum `(m ṗ, I′ ωˢ + p × m ṗ)` has the rate
`(f, τ + p × f)` at `t` exactly when `f = d/dt (m ṗ)` (4.12) and
`I′ ω̇ˢ + ωˢ × I′ ωˢ = τ` (4.13). -/
theorem newtonEuler_spatial_iff {R : ℝ → Rotation} {A : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hR : HasDerivAt (fun s => (R s).val) A t) (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ)
    {p pd ω : ℝ → Vec3} {ω' : Vec3} (hω0 : ω t = Rotation.spatialAngularVelocity R A t hR)
    (hω : HasDerivAt ω ω' t) (hp : HasDerivAt p (pd t) t) (f τ : Vec3) :
    (HasDerivAt (fun s => m • pd s) f t ∧
        HasDerivAt (fun s => inertiaAct (spatialInertia (R s) 𝓘) (ω s) + Vec3.cross (p s) (m • pd s))
          (τ + Vec3.cross (p t) f) t) ↔
      (HasDerivAt (fun s => m • pd s) f t ∧
        inertiaAct (spatialInertia (R t) 𝓘) ω' +
          Vec3.cross (ω t) (inertiaAct (spatialInertia (R t) 𝓘) (ω t)) = τ) := by
  have hL := hasDerivAt_spatialAngularMomentum hR 𝓘 hω0 hω
  have hz : Vec3.cross (pd t) (m • pd t) = 0 := by
    rw [Vec3.cross_smul, Vec3.cross_self', smul_zero]
  constructor
  · rintro ⟨hf, hO⟩
    refine ⟨hf, ?_⟩
    have e := (hL.add (Vec3.hasDerivAt_cross hp hf)).unique hO
    rw [hz, zero_add] at e
    exact add_right_cancel e
  · rintro ⟨hf, he⟩
    refine ⟨hf, ?_⟩
    have h := hL.add (Vec3.hasDerivAt_cross hp hf)
    rw [hz, zero_add, he] at h
    exact h

end RigidBody
end RoboLean
