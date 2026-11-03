import RoboLean.Surfaces.ObjectChartTransfer
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The frame angle of a change of chart is differentiable (MLS pp. 248–250)

MLS Chapter 5, printed pp. 248–249: the contact angle `ψ` is "the angle between the tangent vectors
`∂c_f/∂u_f` and `∂c_o/∂u_o`", so it depends on the charts; p. 243: "it may take several coordinate
charts to completely describe the surface". The library's transfer of Theorem 5.11 (p. 250) across a
change of the finger chart, and of the object chart, takes the angle `θ(s)` between the two
normalized Gauss frames along the motion as a hypothesis with a derivative.

**Proved here.** For two orthogonal charts `c`, `c'` (twice continuously differentiable, the
library's `IsOrthogonalChartOn`) and parameter curves `α(s)`, `β(s)` with derivatives at `t`,
`α(t)`, `β(t)` in the chart domains, describing the same points with the same Gauss normal near `t`,
there is an angle `θ(s)`, with a derivative at `t`, such that near `t` the contact frames satisfy
`g_{c'}(β(s)) = g_c(α(s)) (0, R_z(θ(s)))` (`exists_frameAngle`). Construction: by the library's
frame-change lemma the frames differ by some `R_z(θ_s)`, and `cos θ_s = x(s)ᵀ x'(s)`,
`sin θ_s = y(s)ᵀ x'(s)` for the normalized partials `x = c_u/‖c_u‖`, `y = c_v/‖c_v‖`, `x' = c'_u/‖c'_u‖`;
these are differentiable at `t`, and `θ(s) = θ(t) + arcsin(sin θ_s cos θ(t) − cos θ_s sin θ(t))`
is a differentiable choice near `t`. Hence the transfers of (5.28) hold without the angle hypothesis
(`kinematicEquations_of_finger_chart`, `kinematicEquations_of_object_chart`).

**Reading.** "`C¹` where the charts overlap" is formalized as what the transfers use: a derivative at
the time `t` and the frame relation near `t`; the angle is a local choice (it is determined up to
multiples of `2π`).

**Conventions.** As the library's contact kinematics: `contactFrame`, `gaussFrame`, `frameX`,
`frameY`, `R_z(θ)` as `Rotation.zRotation θ`.
-/

noncomputable section

open Matrix Filter Topology Real

namespace RoboLean
namespace Rolling

open Surface

/-- The cosine and sine of the frame angle as inner products of the normalized partials
(supporting lemma for MLS pp. 248–249). -/
private lemma frame_cos_sin {c c' : (Fin 2 → ℝ) → Vec3} {α β : Fin 2 → ℝ} {θ : ℝ}
    (h : IsOrthogonalAt c α) (hu : partialU c α ≠ 0) (hv : partialV c α ≠ 0)
    (h' : IsOrthogonalAt c' β) (hu' : partialU c' β ≠ 0) (hv' : partialV c' β ≠ 0)
    (hR : gaussFrame c' β = gaussFrame c α * Rotation.zRotation θ) :
    cos θ = inner ℝ (frameX c α) (frameX c' β) ∧ sin θ = inner ℝ (frameY c α) (frameX c' β) := by
  have e : (Rotation.zRotation θ).act (WithLp.toLp 2 ![1, 0, 0]) =
      (gaussFrame c α)⁻¹.act (frameX c' β) := by
    rw [← gaussFrame_act_axisX h' hu' hv', hR, Rotation.act_mul, Rotation.inv_act_act]
  rw [gaussFrame_inv_act h hu hv] at e
  have e0 := congrArg (fun v : Vec3 => v 0) e
  have e1 := congrArg (fun v : Vec3 => v 1) e
  simp [Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at e0 e1
  exact ⟨e0, e1⟩

/-- `R_z(θ)` depends only on `cos θ` and `sin θ` (supporting lemma for MLS p. 248). -/
private lemma zRotation_eq_of_cos_sin {θ φ : ℝ} (hc : cos θ = cos φ) (hs : sin θ = sin φ) :
    Rotation.zRotation θ = Rotation.zRotation φ := by
  apply Subtype.ext
  rw [Rotation.zRotation_val, Rotation.zRotation_val, hc, hs]

/-- **The frame angle of a change of chart has a derivative (MLS pp. 248–249, with p. 243):** for
orthogonal charts `(c, U)` and `(c', U')`, parameter curves `α`, `β` with derivatives at `t`,
`α(t) ∈ U`, `β(t) ∈ U'`, and `c'(β(s)) = c(α(s))` with equal Gauss normals for `s` near `t`, there is
an angle `θ(s)` with a derivative at `t` such that `g_{c'}(β(s)) = g_c(α(s)) (0, R_z(θ(s)))` for `s`
near `t`. -/
theorem exists_frameAngle {c c' : (Fin 2 → ℝ) → Vec3} {U U' : Set (Fin 2 → ℝ)}
    (h : IsOrthogonalChartOn c U) (h' : IsOrthogonalChartOn c' U') {α β : ℝ → Fin 2 → ℝ}
    {α' β' : Fin 2 → ℝ} {t : ℝ} (hα : HasDerivAt α α' t) (hβ : HasDerivAt β β' t)
    (hαU : α t ∈ U) (hβU : β t ∈ U') (hp : ∀ᶠ s in 𝓝 t, c' (β s) = c (α s))
    (hn : ∀ᶠ s in 𝓝 t, gaussNormal c' (β s) = gaussNormal c (α s)) :
    ∃ (θ : ℝ → ℝ) (θ' : ℝ), HasDerivAt θ θ' t ∧
      ∀ᶠ s in 𝓝 t, contactFrame c' (β s) = contactFrame c (α s) * ⟨Rotation.zRotation (θ s), 0⟩ := by
  -- the inner products and their derivatives
  set C : ℝ → ℝ := fun s => inner ℝ (frameX c (α s)) (frameX c' (β s)) with hCdef
  set S : ℝ → ℝ := fun s => inner ℝ (frameY c (α s)) (frameX c' (β s)) with hSdef
  have hfx : ∀ {d : (Fin 2 → ℝ) → Vec3} {V : Set (Fin 2 → ℝ)} {γ : ℝ → Fin 2 → ℝ} {γ' : Fin 2 → ℝ},
      IsOrthogonalChartOn d V → HasDerivAt γ γ' t → γ t ∈ V →
      DifferentiableAt ℝ (fun s => frameX d (γ s)) t ∧
        DifferentiableAt ℝ (fun s => frameY d (γ s)) t := by
    intro d V γ γ' hd hγ hγV
    have hU := differentiableAt_partialU (hd.contDiffAt hγV)
    have hV := differentiableAt_partialV (hd.contDiffAt hγV)
    have hu := hd.partialU_ne_zero hγV
    have hv := hd.partialV_ne_zero hγV
    refine ⟨?_, ?_⟩
    · exact (((hU.norm ℝ hu).inv (norm_ne_zero_iff.2 hu)).smul hU).comp t hγ.differentiableAt
    · exact (((hV.norm ℝ hv).inv (norm_ne_zero_iff.2 hv)).smul hV).comp t hγ.differentiableAt
  obtain ⟨hx, hy⟩ := hfx h hα hαU
  obtain ⟨hx', -⟩ := hfx h' hβ hβU
  have hCd : DifferentiableAt ℝ C t := hx.inner ℝ hx'
  have hSd : DifferentiableAt ℝ S t := hy.inner ℝ hx'
  -- near `t` the frames differ by a rotation with cosine `C` and sine `S`
  have hαev : ∀ᶠ s in 𝓝 t, α s ∈ U := hα.continuousAt.preimage_mem_nhds (h.isOpen.mem_nhds hαU)
  have hβev : ∀ᶠ s in 𝓝 t, β s ∈ U' := hβ.continuousAt.preimage_mem_nhds (h'.isOpen.mem_nhds hβU)
  have hrot : ∀ᶠ s in 𝓝 t, ∀ φ : ℝ, cos φ = C s → sin φ = S s →
      gaussFrame c' (β s) = gaussFrame c (α s) * Rotation.zRotation φ := by
    filter_upwards [hαev, hβev, hn] with s hs hs' hns
    intro φ hcφ hsφ
    obtain ⟨θs, hθs⟩ := exists_gaussFrame_eq_mul_zRotation (h.orthogonal _ hs)
      (h.partialU_ne_zero hs) (h.partialV_ne_zero hs) (h'.orthogonal _ hs')
      (h'.partialU_ne_zero hs') (h'.partialV_ne_zero hs') hns
    obtain ⟨e1, e2⟩ := frame_cos_sin (h.orthogonal _ hs) (h.partialU_ne_zero hs)
      (h.partialV_ne_zero hs) (h'.orthogonal _ hs') (h'.partialU_ne_zero hs')
      (h'.partialV_ne_zero hs') hθs
    rw [hθs, zRotation_eq_of_cos_sin (θ := θs) (φ := φ) (by rw [e1, hcφ]) (by rw [e2, hsφ])]
  have hunit : ∀ᶠ s in 𝓝 t, C s ^ 2 + S s ^ 2 = 1 := by
    filter_upwards [hαev, hβev, hn] with s hs hs' hns
    obtain ⟨θs, hθs⟩ := exists_gaussFrame_eq_mul_zRotation (h.orthogonal _ hs)
      (h.partialU_ne_zero hs) (h.partialV_ne_zero hs) (h'.orthogonal _ hs')
      (h'.partialU_ne_zero hs') (h'.partialV_ne_zero hs') hns
    obtain ⟨e1, e2⟩ := frame_cos_sin (h.orthogonal _ hs) (h.partialU_ne_zero hs)
      (h.partialV_ne_zero hs) (h'.orthogonal _ hs') (h'.partialU_ne_zero hs')
      (h'.partialV_ne_zero hs') hθs
    change inner ℝ _ _ ^ 2 + inner ℝ _ _ ^ 2 = 1
    rw [← e1, ← e2, cos_sq_add_sin_sq]
  -- the angle at `t` and the local choice
  have hu0 : C t ^ 2 + S t ^ 2 = 1 := hunit.self_of_nhds
  obtain ⟨θ₀, hc₀, hs₀⟩ : ∃ θ₀ : ℝ, cos θ₀ = C t ∧ sin θ₀ = S t := by
    let w : ℂ := ⟨C t, S t⟩
    have hw : ‖w‖ = 1 := by
      rw [Complex.norm_def]
      change √(C t * C t + S t * S t) = 1
      rw [show C t * C t + S t * S t = 1 by linear_combination hu0, sqrt_one]
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hw
      norm_num at hw
    exact ⟨w.arg, by simpa [hw] using Complex.cos_arg hw0, by simpa [hw] using Complex.sin_arg w⟩
  set g : ℝ → ℝ := fun s => S s * C t - C s * S t with hgdef
  set k : ℝ → ℝ := fun s => C s * C t + S s * S t with hkdef
  have hgt : g t = 0 := by simp only [hgdef]; ring
  have hkt : k t = 1 := by simp only [hkdef]; linear_combination hu0
  have hgd : DifferentiableAt ℝ g t := (hSd.mul_const _).sub (hCd.mul_const _)
  have hkc : ContinuousAt k t :=
    ((hCd.mul_const _).add (hSd.mul_const _)).continuousAt
  have hkpos : ∀ᶠ s in 𝓝 t, 0 < k s := hkc.eventually (lt_mem_nhds (by rw [hkt]; norm_num))
  have hgk : ∀ᶠ s in 𝓝 t, g s ^ 2 + k s ^ 2 = 1 := by
    filter_upwards [hunit] with s hs
    simp only [hgdef, hkdef]
    linear_combination (C t ^ 2 + S t ^ 2) * hs + hu0
  refine ⟨fun s => θ₀ + arcsin (g s), 1 / √(1 - g t ^ 2) * deriv g t, ?_, ?_⟩
  · have ha := hasDerivAt_arcsin (x := g t) (by rw [hgt]; norm_num) (by rw [hgt]; norm_num)
    exact (ha.comp t hgd.hasDerivAt).const_add θ₀
  · filter_upwards [hrot, hp, hkpos, hgk] with s hr hps hk hgk
    have hg1 : -1 ≤ g s ∧ g s ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (k s)]
    have hsin : sin (arcsin (g s)) = g s := sin_arcsin hg1.1 hg1.2
    have hcos : cos (arcsin (g s)) = k s := by
      rw [cos_arcsin, show 1 - g s ^ 2 = k s ^ 2 by linarith, sqrt_sq hk.le]
    refine contactFrame_eq_mul_zRotation hps (hr _ ?_ ?_)
    · rw [cos_add, hsin, hcos, hc₀, hs₀]
      simp only [hgdef, hkdef]
      linear_combination C s * hu0
    · rw [sin_add, hsin, hcos, hc₀, hs₀]
      simp only [hgdef, hkdef]
      linear_combination S s * hu0

/-- **MLS Theorem 5.11 (p. 250) across a change of the finger chart, with the frame angle
constructed:** under the hypotheses of the library's finger-chart transfer, with the frame relation
replaced by `c'_f(β(s)) = c_f(α_f(s))` with equal Gauss normals near `t` for an orthogonal chart
`(c'_f, U'_f)` and `β` with a derivative at `t`, `β(t) ∈ U'_f`, there are an angle `θ` with the
derivative `θ̇` at `t` and `g_{c'_f}(β(s)) = g_{c_f}(α_f(s)) (0, R_z(θ(s)))` near `t` such that, where
`K_f + K̃_o` is invertible at angle `ψ(t) − θ(t)`, the motion satisfies (5.28) in the chart `c_f` with
angle `ψ − θ` and angle rate `ψ̇ − θ̇`. -/
theorem kinematicEquations_of_finger_chart {cf cf' co : (Fin 2 → ℝ) → Vec3}
    {Uf Uf' Uo : Set (Fin 2 → ℝ)} (hf : IsOrthogonalChartOn cf Uf)
    (hf' : IsOrthogonalChartOn cf' Uf') (ho : IsOrthogonalChartOn co Uo)
    {αf βf αo : ℝ → Fin 2 → ℝ} {ψ : ℝ → ℝ} {αf' βf' αo' : Fin 2 → ℝ} {ψ' t : ℝ}
    (hαf : HasDerivAt αf αf' t) (hβf : HasDerivAt βf βf' t) (hαo : HasDerivAt αo αo' t)
    (hψ : HasDerivAt ψ ψ' t) (hft : αf t ∈ Uf) (hft' : βf t ∈ Uf') (hot : αo t ∈ Uo)
    (hp : ∀ᶠ s in 𝓝 t, cf' (βf s) = cf (αf s))
    (hn : ∀ᶠ s in 𝓝 t, gaussNormal cf' (βf s) = gaussNormal cf (αf s))
    {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t, g s = relativePose cf' co (βf s) (αo s) (ψ s)) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    ∃ (θ : ℝ → ℝ) (θ' : ℝ), HasDerivAt θ θ' t ∧
      (∀ᶠ s in 𝓝 t,
        contactFrame cf' (βf s) = contactFrame cf (αf s) * ⟨Rotation.zRotation (θ s), 0⟩) ∧
      (IsUnit (relativeCurvature (curvatureTensor cf (αf t)) (curvatureTensor co (αo t))
        (ψ t - θ t)).det →
      KinematicEquations (metricTensor cf (αf t)) (curvatureTensor cf (αf t))
        (metricTensor co (αo t)) (curvatureTensor co (αo t)) (torsionForm cf (αf t))
        (torsionForm co (αo t)) (ψ t - θ t) αf' αo' (ψ' - θ')
        (Twist.adjoint (contactFrame cf (αf t))⁻¹ (RigidTransform.bodyVelocity g D t hD))) := by
  obtain ⟨θ, θ', hθ, hframe⟩ := exists_frameAngle hf hf' hαf hβf hft hft' hp hn
  exact ⟨θ, θ', hθ, hframe, fun hX => kinematicEquations_of_finger_frame hf ho hαf hαo hψ hθ hft hot hframe hX
    hg hD⟩

/-- **MLS Theorem 5.11 (p. 250) across a change of the object chart, with the frame angle
constructed:** under the hypotheses of `kinematicEquations_of_object_frame`, with the frame relation
replaced by `c'_o(β(s)) = c_o(α_o(s))` with equal Gauss normals near `t` for an orthogonal chart
`(c'_o, U'_o)` and `β` with a derivative at `t`, `β(t) ∈ U'_o`, there are an angle `θ` with the
derivative `θ̇` at `t` and `g_{c'_o}(β(s)) = g_{c_o}(α_o(s)) (0, R_z(θ(s)))` near `t` such that, where
`K_f + K̃_o` is invertible at angle `ψ(t) − θ(t)`, the motion satisfies (5.28) in the chart `c_o` with
angle `ψ − θ` and angle rate `ψ̇ − θ̇`. -/
theorem kinematicEquations_of_object_chart {cf co co' : (Fin 2 → ℝ) → Vec3}
    {Uf Uo Uo' : Set (Fin 2 → ℝ)} (hf : IsOrthogonalChartOn cf Uf)
    (ho : IsOrthogonalChartOn co Uo) (ho' : IsOrthogonalChartOn co' Uo')
    {αf αo βo : ℝ → Fin 2 → ℝ} {ψ : ℝ → ℝ} {αf' αo' βo' : Fin 2 → ℝ} {ψ' t : ℝ}
    (hαf : HasDerivAt αf αf' t) (hαo : HasDerivAt αo αo' t) (hβo : HasDerivAt βo βo' t)
    (hψ : HasDerivAt ψ ψ' t) (hft : αf t ∈ Uf) (hot : αo t ∈ Uo) (hot' : βo t ∈ Uo')
    (hp : ∀ᶠ s in 𝓝 t, co' (βo s) = co (αo s))
    (hn : ∀ᶠ s in 𝓝 t, gaussNormal co' (βo s) = gaussNormal co (αo s))
    {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t, g s = relativePose cf co' (αf s) (βo s) (ψ s)) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    ∃ (θ : ℝ → ℝ) (θ' : ℝ), HasDerivAt θ θ' t ∧
      (∀ᶠ s in 𝓝 t,
        contactFrame co' (βo s) = contactFrame co (αo s) * ⟨Rotation.zRotation (θ s), 0⟩) ∧
      (IsUnit (relativeCurvature (curvatureTensor cf (αf t)) (curvatureTensor co (αo t))
        (ψ t - θ t)).det →
      KinematicEquations (metricTensor cf (αf t)) (curvatureTensor cf (αf t))
        (metricTensor co (αo t)) (curvatureTensor co (αo t)) (torsionForm cf (αf t))
        (torsionForm co (αo t)) (ψ t - θ t) αf' αo' (ψ' - θ')
        (Twist.adjoint (contactFrame cf (αf t))⁻¹ (RigidTransform.bodyVelocity g D t hD))) := by
  obtain ⟨θ, θ', hθ, hframe⟩ := exists_frameAngle ho ho' hαo hβo hot hot' hp hn
  exact ⟨θ, θ', hθ, hframe, fun hX => kinematicEquations_of_object_frame hf ho hαf hαo hψ hθ hft hot hframe hX
    hg hD⟩

end Rolling
end RoboLean
