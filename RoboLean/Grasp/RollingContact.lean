import RoboLean.Grasp.ContactEquations

/-!
# Kinematics of rolling contact (MLS Theorem 5.11 and Corollary 5.11.1)

MLS Chapter 5, §6.2, printed pp. 249–252: Theorem 5.11 (Montana's kinematic equations of contact),
its proof (5.29)–(5.37), and Corollary 5.11.1 (5.38).

**What MLS states.** "We describe the motion of `O` and `F` at time `t` using local coordinate
frames `L_o(t)` and `L_f(t)`. Let `v_{l_o l_f} = (v_x, v_y, v_z)` be the components of the (body)
translational velocity of `L_f(t)` relative to `L_o(t)` at time `t`. Similarly, let
`ω_{l_o l_f} = (ω_x, ω_y, ω_z)` be the (body) rotational velocity ... As long as the two bodies
remain in contact, `v_z = 0`" (p. 249), and `V_{l_o l_f} = Ad⁻¹_{g_{f l_f}} V_of` (5.27, p. 250).
**Theorem 5.11 (Kinematic equations of contact [72]).** "The motion of the contact coordinates,
`η̇`, as a function of the relative motion is given by" (5.28) (p. 250), under the standing
assumption that "all manipulation occurs in an open set on which the relative curvature is
invertible" (p. 251). The proof combines `V_{f c_f} = V_{l_f c_f}` (5.29), `V_{o c_o} = V_{l_o c_o}`
(5.30), (5.31) and (5.32) into
`V_{l_o l_f} + V_{f c_f} = diag(R_{c_o c_f}ᵀ, R_{c_o c_f}ᵀ) V_{o c_o} + V_{c_o c_f}` (5.33),
substitutes (5.34)–(5.36) and equates components (5.37) (pp. 251–252). **Corollary 5.11.1.** "The
contact coordinates for rolling contact evolve according to" (5.38) (p. 252).

**Formalized, in the form of the library's (5.8)–(5.13).** The motion is a pose curve `g` that
agrees near `t` with the relative pose `g_of(η(s))` of contact coordinates `η = (α_f, α_o, ψ)` with
actual derivatives at `t`, the charts orthogonal (`IsOrthogonalChartOn`) and `α_f(t) ∈ U_f`,
`α_o(t) ∈ U_o`. For every derivative `D` of `g` at `t`, with `V_of = bodyVelocity g D t` and
`V_{l_o l_f} = Ad⁻¹_{g_{f c_f}(α_f(t))} V_of` (the local frame frozen at time `t`):

* (5.33) with (5.34)–(5.36) substituted holds (`relativeVelocity_add_contactFrameVelocity`);
* (5.37) holds, in particular `v_z = 0`, which is derived, not assumed
  (`contactEquations_of_hasDerivAt`);
* **Theorem 5.11:** if the relative curvature form `K_f + K̃_o` is invertible at `η(t)`, (5.28)
  holds (`kinematicEquations_of_hasDerivAt`);
* **Corollary 5.11.1:** under pure rolling (`IsRolling`, p. 249), (5.38) holds
  (`rollingEquations_of_hasDerivAt`);
* the derivative-level core of Proposition 5.12: with `K_f + K̃_o` invertible, a zero relative
  velocity forces zero contact rates (`rates_eq_zero_of_bodyVelocity_eq_zero`).

The conventions are those of `RoboLean.Rolling`: `R_ψ` as printed on p. 250, the contact rotation
`diag(R_ψ, −1)` (the printed (5.34) has `+1`), the book's Gauss normals with no orientation
hypothesis, twist order `(v, ω)`. The existence of a derivative of `g_of(η(t))` is
`exists_hasDerivAt_relativePose`. Nothing here concerns forces, friction or the persistence of
contact.
-/

noncomputable section

open Matrix Filter Topology Real

namespace RoboLean
namespace Rolling

open Surface

variable {cf co : (Fin 2 → ℝ) → Vec3} {Uf Uo : Set (Fin 2 → ℝ)} {αf αo : ℝ → Fin 2 → ℝ}
  {ψ : ℝ → ℝ} {αf' αo' : Fin 2 → ℝ} {ψ' t : ℝ}

/-- Supporting lemma (MLS p. 249, the relative motion is a curve in `SE(3)`): a homogeneous matrix
curve that agrees near `t` with one having the derivative `D` has the derivative `D`. -/
private theorem hasDerivAt_homogeneous_congr {f₁ f : ℝ → HomogeneousMatrix} {D : HomogeneousMatrix}
    (h : HasDerivAt f D t) (h₁ : f₁ =ᶠ[𝓝 t] f) : HasDerivAt f₁ D t := by
  refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
  refine (hasDerivAt_pi.mp (hasDerivAt_pi.mp h i) j).congr_of_eventuallyEq ?_
  filter_upwards [h₁] with s hs
  rw [hs]

/-- Supporting lemma (MLS p. 249): a homogeneous matrix curve has at most one derivative. -/
private theorem homogeneous_hasDerivAt_unique {f : ℝ → HomogeneousMatrix} {D E : HomogeneousMatrix}
    (hD : HasDerivAt f D t) (hE : HasDerivAt f E t) : D = E := by
  ext i j
  exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hD i) j).unique
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hE i) j)

/-- Supporting lemma (MLS eq. (2.60), p. 55): the body velocity depends only on the pose at `t` and
the derivative, not on the curve away from `t`. -/
private theorem bodyVelocity_congr {g h : ℝ → RigidTransform} {D : HomogeneousMatrix}
    (hg : HasDerivAt (fun s => (g s).toHomogeneous) D t)
    (hh : HasDerivAt (fun s => (h s).toHomogeneous) D t) (he : g t = h t) :
    RigidTransform.bodyVelocity g D t hg = RigidTransform.bodyVelocity h D t hh := by
  apply Twist.hat_injective
  rw [RigidTransform.hat_bodyVelocity, RigidTransform.hat_bodyVelocity, he]

/-- The inverse contact rotation in coordinates, `diag(R_ψ, −1)ᵀ w = (R_ψ (w_x, w_y), −w_z)`
(supporting lemma for MLS eq. (5.33), p. 251). -/
private theorem contactRotation_inv_act (ψ : ℝ) (w : Vec3) :
    (contactRotation ψ)⁻¹.act w =
      WithLp.toLp 2 ![cos ψ * w 0 - sin ψ * w 1, -sin ψ * w 0 - cos ψ * w 1, -w 2] := by
  apply WithLp.ofLp_injective
  ext i
  rw [Rotation.act_apply, Rotation.inv_val]
  fin_cases i <;>
    simp [contactRotation, contactRotationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- The derivatives of the three pose curves along a motion of the contact coordinates (supporting
lemma for MLS Theorem 5.11, p. 250). -/
private theorem exists_derivs (hf : IsOrthogonalChartOn cf Uf) (ho : IsOrthogonalChartOn co Uo)
    (hαf : HasDerivAt αf αf' t) (hαo : HasDerivAt αo αo' t) (hψ : HasDerivAt ψ ψ' t)
    (hft : αf t ∈ Uf) (hot : αo t ∈ Uo) :
    ∃ DA DB DC : HomogeneousMatrix,
      HasDerivAt (fun s => (contactFrame co (αo s)).toHomogeneous) DA t ∧
      HasDerivAt (fun s => (contactOffset (ψ s)).toHomogeneous) DB t ∧
      HasDerivAt (fun s => (contactFrame cf (αf s)).toHomogeneous) DC t := by
  obtain ⟨DA, hA⟩ := exists_hasDerivAt_contactFrame ho hαo hot
  obtain ⟨DB, hB⟩ := exists_hasDerivAt_contactOffset hψ
  obtain ⟨DC, hC⟩ := exists_hasDerivAt_contactFrame hf hαf hft
  exact ⟨DA, DB, DC, hA, hB, hC⟩

/-- **The relative pose along a motion of the contact coordinates has a derivative (MLS p. 249):**
for orthogonal charts and contact coordinates `η = (α_f, α_o, ψ)` with actual derivatives at `t`
inside the chart domains, `t ↦ g_of(η(t))` has a derivative at `t`. -/
theorem exists_hasDerivAt_relativePose (hf : IsOrthogonalChartOn cf Uf)
    (ho : IsOrthogonalChartOn co Uo) (hαf : HasDerivAt αf αf' t) (hαo : HasDerivAt αo αo' t)
    (hψ : HasDerivAt ψ ψ' t) (hft : αf t ∈ Uf) (hot : αo t ∈ Uo) :
    ∃ D : HomogeneousMatrix,
      HasDerivAt (fun s => (relativePose cf co (αf s) (αo s) (ψ s)).toHomogeneous) D t := by
  obtain ⟨DA, DB, DC, hA, hB, hC⟩ := exists_derivs hf ho hαf hαo hψ hft hot
  exact ⟨_, RigidTransform.hasDerivAt_toHomogeneous_mul
    (RigidTransform.hasDerivAt_toHomogeneous_mul hA hB)
    (RigidTransform.hasDerivAt_toHomogeneous_inv hC)⟩

/-- **MLS eq. (5.33), p. 251, with (5.34)–(5.36) substituted:** along a motion `g` that agrees near
`t` with `g_of(η(s))`, for every derivative `D` of `g`, the relative velocity
`V_{l_o l_f} = Ad⁻¹_{g_{f c_f}(α_f(t))} V_of` satisfies
`V_{l_o l_f} + V_{f c_f} = Ad⁻¹_{g_{c_o c_f}} V_{o c_o} + V_{c_o c_f}`, with `V_{f c_f}` and
`V_{o c_o}` the Lemma 5.10 twists of the two charts and `V_{c_o c_f} = (0, (0, 0, ψ̇))` (5.34). -/
theorem relativeVelocity_add_contactFrameVelocity (hf : IsOrthogonalChartOn cf Uf)
    (ho : IsOrthogonalChartOn co Uo) (hαf : HasDerivAt αf αf' t) (hαo : HasDerivAt αo αo' t)
    (hψ : HasDerivAt ψ ψ' t) (hft : αf t ∈ Uf) (hot : αo t ∈ Uo) {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t, g s = relativePose cf co (αf s) (αo s) (ψ s)) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    Twist.adjoint (contactFrame cf (αf t))⁻¹ (RigidTransform.bodyVelocity g D t hD) +
        contactFrameVelocity cf (αf t) αf' =
      Twist.adjoint (contactOffset (ψ t))⁻¹ (contactFrameVelocity co (αo t) αo') +
        ⟨0, WithLp.toLp 2 ![0, 0, ψ']⟩ := by
  obtain ⟨DA, DB, DC, hA, hB, hC⟩ := exists_derivs hf ho hαf hαo hψ hft hot
  have hAB := RigidTransform.hasDerivAt_toHomogeneous_mul hA hB
  have hCi := RigidTransform.hasDerivAt_toHomogeneous_inv hC
  have hP := RigidTransform.hasDerivAt_toHomogeneous_mul hAB hCi
  -- the derivative of `g` is the derivative of the relative pose
  have hgeq : (fun s => (g s).toHomogeneous) =ᶠ[𝓝 t]
      (fun s => (relativePose cf co (αf s) (αo s) (ψ s)).toHomogeneous) := by
    filter_upwards [hg] with s hs
    rw [hs]
  have hD' : HasDerivAt (fun s => (relativePose cf co (αf s) (αo s) (ψ s)).toHomogeneous) D t :=
    hasDerivAt_homogeneous_congr hD hgeq.symm
  have hDP := homogeneous_hasDerivAt_unique hD' hP
  rw [bodyVelocity_congr hD hD' hg.self_of_nhds]
  -- Proposition 2.15 twice and Lemma 2.16
  have hmul : RigidTransform.bodyVelocity
      (fun s => relativePose cf co (αf s) (αo s) (ψ s)) D t hD' =
      Twist.adjoint ((contactFrame cf (αf t))⁻¹)⁻¹
          (Twist.adjoint (contactOffset (ψ t))⁻¹
              (RigidTransform.bodyVelocity _ DA t hA) +
            RigidTransform.bodyVelocity _ DB t hB) +
        RigidTransform.bodyVelocity (fun s => (contactFrame cf (αf s))⁻¹) _ t hCi := by
    subst hDP
    rw [← RigidTransform.bodyVelocity_mul hA hB]
    exact RigidTransform.bodyVelocity_mul hAB hCi
  have hinv := RigidTransform.bodyVelocity_eq_neg_adjoint_bodyVelocity_inv hC
  rw [hmul, inv_inv, Twist.adjoint_add, Twist.adjoint_inv_adjoint,
    bodyVelocity_contactFrame ho hαo hot hA,
    bodyVelocity_contactOffset hψ hB, ← bodyVelocity_contactFrame hf hαf hft hC, hinv]
  abel

/-- **MLS eq. (5.37), p. 252, along a motion (the components of (5.33)):** for orthogonal charts,
contact coordinates `η = (α_f, α_o, ψ)` with actual derivatives at `t` inside the chart domains, and
a pose curve `g` agreeing near `t` with `g_of(η(s))`, every derivative `D` of `g` gives a relative
velocity `V_{l_o l_f} = Ad⁻¹_{g_{f c_f}(α_f(t))} V^b_of` that satisfies (5.37) with the geometric
parameters at `η(t)`; in particular `v_z = 0`. No invertibility is needed. -/
theorem contactEquations_of_hasDerivAt (hf : IsOrthogonalChartOn cf Uf)
    (ho : IsOrthogonalChartOn co Uo) (hαf : HasDerivAt αf αf' t) (hαo : HasDerivAt αo αo' t)
    (hψ : HasDerivAt ψ ψ' t) (hft : αf t ∈ Uf) (hot : αo t ∈ Uo) {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t, g s = relativePose cf co (αf s) (αo s) (ψ s)) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    ContactEquations (metricTensor cf (αf t)) (curvatureTensor cf (αf t))
      (metricTensor co (αo t)) (curvatureTensor co (αo t)) (torsionForm cf (αf t))
      (torsionForm co (αo t)) (ψ t) αf' αo' ψ'
      (Twist.adjoint (contactFrame cf (αf t))⁻¹ (RigidTransform.bodyVelocity g D t hD)) := by
  have h := relativeVelocity_add_contactFrameVelocity hf ho hαf hαo hψ hft hot hg hD
  set V := Twist.adjoint (contactFrame cf (αf t))⁻¹ (RigidTransform.bodyVelocity g D t hD)
  have hV : V = Twist.adjoint (contactOffset (ψ t))⁻¹ (contactFrameVelocity co (αo t) αo') +
      ⟨0, WithLp.toLp 2 ![0, 0, ψ']⟩ - contactFrameVelocity cf (αf t) αf' := by
    rw [← h]
    abel
  have hlin : ∀ i, V.linear i = ((contactRotation (ψ t))⁻¹.act
      (contactFrameVelocity co (αo t) αo').linear - (contactFrameVelocity cf (αf t) αf').linear) i
      := by
    intro i
    rw [hV, Twist.adjoint_inv]
    simp [contactOffset]
  have hang : ∀ i, V.angular i = ((contactRotation (ψ t))⁻¹.act
      (contactFrameVelocity co (αo t) αo').angular + WithLp.toLp 2 ![0, 0, ψ'] -
      (contactFrameVelocity cf (αf t) αf').angular) i := by
    intro i
    rw [hV, Twist.adjoint_inv]
    simp [contactOffset]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext i
    fin_cases i <;>
      simp [hlin, contactRotation_inv_act, contactFrameVelocity, angleMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two] <;> ring
  · simp [hlin, contactRotation_inv_act, contactFrameVelocity]
  · funext i
    fin_cases i <;>
      simp [hang, contactRotation_inv_act, contactFrameVelocity, angleMatrix, Matrix.mulVec,
        Matrix.vecMul, Matrix.mul_apply, dotProduct, Fin.sum_univ_two] <;> ring
  · simp [hang, contactRotation_inv_act, contactFrameVelocity]
    ring

/-- **MLS Theorem 5.11, printed p. 250: the kinematic equations of contact (5.28).** For orthogonal
charts `(c_f, U_f)`, `(c_o, U_o)`, contact coordinates `η = (α_f, α_o, ψ)` with actual derivatives
at `t` inside the chart domains, and a pose curve `g` agreeing near `t` with `g_of(η(s))`, if the
relative curvature form `K_f + K̃_o` is invertible at `η(t)` (the hypothesis of p. 251), then for
every derivative `D` of `g` the contact rates satisfy (5.28) with
`(v, ω) = V^b_{l_o l_f} = Ad⁻¹_{g_{f l_f}} V^b_of`, `g_{f l_f} = g_{f c_f}(α_f(t))`. -/
theorem kinematicEquations_of_hasDerivAt (hf : IsOrthogonalChartOn cf Uf)
    (ho : IsOrthogonalChartOn co Uo) (hαf : HasDerivAt αf αf' t) (hαo : HasDerivAt αo αo' t)
    (hψ : HasDerivAt ψ ψ' t) (hft : αf t ∈ Uf) (hot : αo t ∈ Uo)
    (hX : IsUnit (relativeCurvature (curvatureTensor cf (αf t)) (curvatureTensor co (αo t))
      (ψ t)).det) {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t, g s = relativePose cf co (αf s) (αo s) (ψ s)) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    KinematicEquations (metricTensor cf (αf t)) (curvatureTensor cf (αf t))
      (metricTensor co (αo t)) (curvatureTensor co (αo t)) (torsionForm cf (αf t))
      (torsionForm co (αo t)) (ψ t) αf' αo' ψ'
      (Twist.adjoint (contactFrame cf (αf t))⁻¹ (RigidTransform.bodyVelocity g D t hD)) :=
  (contactEquations_iff_kinematicEquations
    (isUnit_det_metricTensor (hf.partialU_ne_zero hft) (hf.partialV_ne_zero hft))
    (isUnit_det_metricTensor (ho.partialU_ne_zero hot) (ho.partialV_ne_zero hot)) hX).mp
    (contactEquations_of_hasDerivAt hf ho hαf hαo hψ hft hot hg hD)

/-- **MLS Corollary 5.11.1, printed p. 252: the contact coordinates for rolling contact evolve
according to (5.38).** Under the hypotheses of Theorem 5.11 (`kinematicEquations_of_hasDerivAt`), if
the relative velocity `V^b_{l_o l_f}` is a pure rolling (`v_x = v_y = 0`, `ω_z = 0`, p. 249), then
`α̇_f = M_f⁻¹ (K_f + K̃_o)⁻¹ (−ω_y, ω_x)`, `α̇_o = M_o⁻¹ R_ψ (K_f + K̃_o)⁻¹ (−ω_y, ω_x)` and
`ψ̇ = T_f M_f α̇_f + T_o M_o α̇_o`. -/
theorem rollingEquations_of_hasDerivAt (hf : IsOrthogonalChartOn cf Uf)
    (ho : IsOrthogonalChartOn co Uo) (hαf : HasDerivAt αf αf' t) (hαo : HasDerivAt αo αo' t)
    (hψ : HasDerivAt ψ ψ' t) (hft : αf t ∈ Uf) (hot : αo t ∈ Uo)
    (hX : IsUnit (relativeCurvature (curvatureTensor cf (αf t)) (curvatureTensor co (αo t))
      (ψ t)).det) {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t, g s = relativePose cf co (αf s) (αo s) (ψ s)) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t)
    (hr : IsRolling (Twist.adjoint (contactFrame cf (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD))) :
    RollingEquations (metricTensor cf (αf t)) (curvatureTensor cf (αf t))
      (metricTensor co (αo t)) (curvatureTensor co (αo t)) (torsionForm cf (αf t))
      (torsionForm co (αo t)) (ψ t) αf' αo' ψ'
      (Twist.adjoint (contactFrame cf (αf t))⁻¹ (RigidTransform.bodyVelocity g D t hD)) :=
  rollingEquations_of_kinematicEquations
    (kinematicEquations_of_hasDerivAt hf ho hαf hαo hψ hft hot hX hg hD) hr

/-- **The derivative-level core of MLS Proposition 5.12, p. 254, along a motion:** under the
hypotheses of Theorem 5.11, with the relative curvature form invertible at `η(t)`, if the relative
body velocity `V^b_of` vanishes at `t`, then the contact rates `α̇_f`, `α̇_o`, `ψ̇` vanish. -/
theorem rates_eq_zero_of_bodyVelocity_eq_zero (hf : IsOrthogonalChartOn cf Uf)
    (ho : IsOrthogonalChartOn co Uo) (hαf : HasDerivAt αf αf' t) (hαo : HasDerivAt αo αo' t)
    (hψ : HasDerivAt ψ ψ' t) (hft : αf t ∈ Uf) (hot : αo t ∈ Uo)
    (hX : IsUnit (relativeCurvature (curvatureTensor cf (αf t)) (curvatureTensor co (αo t))
      (ψ t)).det) {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t, g s = relativePose cf co (αf s) (αo s) (ψ s)) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t)
    (h0 : RigidTransform.bodyVelocity g D t hD = 0) : αf' = 0 ∧ αo' = 0 ∧ ψ' = 0 := by
  have h := contactEquations_of_hasDerivAt hf ho hαf hαo hψ hft hot hg hD
  rw [h0, Twist.adjoint_zero] at h
  exact ((contactEquations_zero_injective_iff
    (isUnit_det_metricTensor (hf.partialU_ne_zero hft) (hf.partialV_ne_zero hft))
    (isUnit_det_metricTensor (ho.partialU_ne_zero hot) (ho.partialV_ne_zero hot))).mpr hX)
    αf' αo' ψ' h

end Rolling
end RoboLean
