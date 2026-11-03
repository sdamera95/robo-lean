import RoboLean.Surfaces.ContactSet

/-!
# Theorem 5.11 across a change of the object chart (MLS pp. 248–250)

MLS Chapter 5, §6.2, printed pp. 248–250: "For simplicity, we will restrict ourselves to the case
where motion is contained in a single coordinate chart for each object" (p. 248); the contact
coordinates `η = (α_f, α_o, ψ)`, with `ψ` the angle between `∂c_f/∂u_f` and `∂c_o/∂u_o`, depend on
the charts; Theorem 5.11 (p. 250) gives the kinematic equations of contact (5.28).

**Proved here.** The object-chart counterpart of the library's change of the finger chart along a
motion: if a motion is described in an object chart `c'_o` and a second orthogonal object chart
`c_o` covers the same contact points near `t`, with contact frames that differ by `R_z(θ(s))`, then
the same motion satisfies (5.28) in the chart `c_o`, with angle `ψ − θ` and angle rate `ψ̇ − θ̇`
(`kinematicEquations_of_object_frame`). The configuration `g_of` is unchanged; only the contact
angle shifts by the angle between the two object frames, and the finger's contact frame, which
enters the velocity, is unchanged.

**Conventions.** As the library's contact kinematics: `relativePose`, `contactFrame`, Mathlib's
derivatives, `R_z(θ)` as `Rotation.zRotation θ`; the frame angle `θ` along the motion is a
hypothesis with a derivative.
-/

noncomputable section

open Matrix Filter Topology Real

namespace RoboLean
namespace Rolling

open Surface

/-- **MLS Theorem 5.11 (p. 250) transfers across a change of the object chart.** Let a motion be
described in the object chart `c'_o` (a pose curve `g` agreeing near `t` with
`g_of(α_f(s), β(s), ψ(s))`), and let a second orthogonal chart `(c_o, U_o)` cover the same contact
points near `t`, with coordinates `α_o(s) ∈ U_o` whose contact frames differ by `R_z(θ(s))`
(`g_{oc'_o}(β(s)) = g_{oc_o}(α_o(s)) (0, R_z(θ(s)))`). If `α_f`, `α_o`, `ψ` and `θ` have derivatives
at `t` and `K_f + K̃_o` is invertible at `(α_f(t), α_o(t), ψ(t) − θ(t))` in the chart `c_o`, then the
same motion satisfies (5.28) in the chart `c_o`, with angle `ψ − θ` and angle rate `ψ̇ − θ̇`. -/
theorem kinematicEquations_of_object_frame {cf co co' : (Fin 2 → ℝ) → Vec3}
    {Uf Uo : Set (Fin 2 → ℝ)} (hf : IsOrthogonalChartOn cf Uf) (ho : IsOrthogonalChartOn co Uo)
    {αf αo βo : ℝ → Fin 2 → ℝ} {ψ θ : ℝ → ℝ} {αf' αo' : Fin 2 → ℝ} {ψ' θ' t : ℝ}
    (hαf : HasDerivAt αf αf' t) (hαo : HasDerivAt αo αo' t) (hψ : HasDerivAt ψ ψ' t)
    (hθ : HasDerivAt θ θ' t) (hft : αf t ∈ Uf) (hot : αo t ∈ Uo)
    (hframe : ∀ᶠ s in 𝓝 t,
      contactFrame co' (βo s) = contactFrame co (αo s) * ⟨Rotation.zRotation (θ s), 0⟩)
    (hX : IsUnit (relativeCurvature (curvatureTensor cf (αf t)) (curvatureTensor co (αo t))
      (ψ t - θ t)).det) {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t, g s = relativePose cf co' (αf s) (βo s) (ψ s)) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    KinematicEquations (metricTensor cf (αf t)) (curvatureTensor cf (αf t))
      (metricTensor co (αo t)) (curvatureTensor co (αo t)) (torsionForm cf (αf t))
      (torsionForm co (αo t)) (ψ t - θ t) αf' αo' (ψ' - θ')
      (Twist.adjoint (contactFrame cf (αf t))⁻¹ (RigidTransform.bodyVelocity g D t hD)) := by
  have hg' : ∀ᶠ s in 𝓝 t, g s = relativePose cf co (αf s) (αo s) (ψ s - θ s) := by
    filter_upwards [hg, hframe] with s h1 h2
    rw [h1, relativePose_eq_of_object_frame h2]
  exact kinematicEquations_of_hasDerivAt (ψ := fun s => ψ s - θ s) hf ho hαf hαo (hψ.sub hθ) hft
    hot hX hg' hD

end Rolling
end RoboLean
