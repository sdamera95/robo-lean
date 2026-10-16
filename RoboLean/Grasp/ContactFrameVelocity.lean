import RoboLean.Grasp.GeometricParameters
import RoboLean.Geometry.RigidVelocityComposition
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The induced velocity of the contact frame (MLS Lemma 5.10)

MLS Chapter 5, §6.1, printed pp. 246–247, Lemma 5.10, equations (5.25)–(5.26).

**What MLS states.** "Let `p(t) ∈ S` be a curve on the surface of the object and define the contact
frame along the curve to be the frame `C` which coincides with the Gauss frame at time `t` ... We
assume `p(t)` lies in a single coordinate chart `c : U → ℝ³` and we let `α(t) = c⁻¹(p(t))` represent
the local coordinates" (p. 246). **Lemma 5.10 (Induced velocity of the contact frame).** "The (body)
velocity of the contact frame `C` relative to the reference frame `O` of the object is given by
`V^b_oc = (v_oc, ω_oc)` where `v_oc = [M α̇; 0]` (5.25),
`ω̂_oc = [[0, −ω_z, ω_y], [ω_z, 0, −ω_x], [−ω_y, ω_x, 0]]`
`= [[0, −T M α̇ | K M α̇], [T M α̇, 0 | ], [−(K M α̇)ᵀ | 0]]` (5.26), and `M`, `K`, and `T` are the
geometric parameters of the surface relative to the coordinate chart `(c, U)`" (p. 247). The proof
takes `p_oc = c(α(t))`, `R_oc = [x y z]`, `v_oc = R_ocᵀ ṗ_oc` and `ω̂_oc = R_ocᵀ Ṙ_oc`.

**Formalized.** For an orthogonal chart on an open `U` (`IsOrthogonalChartOn`) and a coordinate
curve `α` with an actual derivative `α̇` at `t` and `α(t) ∈ U`, the pose curve
`t ↦ g_oc(t) = contactFrame c (α t)` has a derivative (`exists_hasDerivAt_contactFrame`), and for
every derivative `D` its body velocity (MLS eq. (2.60), the library's `bodyVelocity`, twist order
`(v, ω)`) is `contactFrameVelocity c (α t) α̇` (`bodyVelocity_contactFrame`): linear part
`(M α̇, 0)` and angular part `ω = (−(K M α̇)₂, (K M α̇)₁, T M α̇)`, which is (5.26) read through the
hat map (`hat_angular_contactFrameVelocity`). The normal is the book's `n = c_u × c_v/‖c_u × c_v‖`;
no orientation hypothesis is needed.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Surface

variable {c : (Fin 2 → ℝ) → Vec3} {U : Set (Fin 2 → ℝ)}

/-- **The body velocity of MLS Lemma 5.10, p. 247, eqs. (5.25)–(5.26):** for chart coordinates `α`
and coordinate velocity `α̇`, the twist `(v, ω)` with `v = (M α̇, 0)` and
`ω = (−(K M α̇)₂, (K M α̇)₁, T M α̇)`, `M`, `K`, `T` the geometric parameters at `α` (twist order
`(v, ω)`; components indexed `0, 1, 2` for the book's `x, y, z`). -/
def contactFrameVelocity (c : (Fin 2 → ℝ) → Vec3) (α α' : Fin 2 → ℝ) : Twist :=
  ⟨WithLp.toLp 2 ![(metricTensor c α *ᵥ α') 0, (metricTensor c α *ᵥ α') 1, 0],
    WithLp.toLp 2 ![-(curvatureTensor c α *ᵥ (metricTensor c α *ᵥ α')) 1,
      (curvatureTensor c α *ᵥ (metricTensor c α *ᵥ α')) 0,
      torsionForm c α ⬝ᵥ (metricTensor c α *ᵥ α')]⟩

/-- **MLS eq. (5.26), p. 247, as printed:** the hat matrix of the angular part of the Lemma 5.10
twist is `[[0, −T M α̇, (K M α̇)₁], [T M α̇, 0, (K M α̇)₂], [−(K M α̇)₁, −(K M α̇)₂, 0]]` (book
indices `1, 2` are Lean `0, 1`). -/
theorem hat_angular_contactFrameVelocity (c : (Fin 2 → ℝ) → Vec3) (α α' : Fin 2 → ℝ) :
    Vec3.hat (contactFrameVelocity c α α').angular =
      !![0, -(torsionForm c α ⬝ᵥ (metricTensor c α *ᵥ α')),
          (curvatureTensor c α *ᵥ (metricTensor c α *ᵥ α')) 0;
        torsionForm c α ⬝ᵥ (metricTensor c α *ᵥ α'), 0,
          (curvatureTensor c α *ᵥ (metricTensor c α *ᵥ α')) 1;
        -(curvatureTensor c α *ᵥ (metricTensor c α *ᵥ α')) 0,
          -(curvatureTensor c α *ᵥ (metricTensor c α *ᵥ α')) 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Vec3.hat, contactFrameVelocity]

/-! ### Derivatives of pose curves from their blocks -/

/-- **A pose curve has a derivative when its rotation and translation do (MLS eq. (2.60), p. 55, `ḡ`
with blocks `Ṙ` and `ṗ`):** the derivative of `[R p; 0 1]` is `[Ṙ ṗ; 0 0]`. -/
theorem hasDerivAt_toHomogeneous_of {g : ℝ → RigidTransform} {A : Matrix (Fin 3) (Fin 3) ℝ}
    {v : Vec3} {t : ℝ} (hR : HasDerivAt (fun s => (g s).rotation.val) A t)
    (hp : HasDerivAt (fun s => (g s).translation) v t) :
    HasDerivAt (fun s => (g s).toHomogeneous) (Matrix.fromBlocks A (Matrix.of fun i _ => v i) 0 0)
      t := by
  refine hasDerivAt_pi.mpr fun r => hasDerivAt_pi.mpr fun q => ?_
  rcases r with i | i <;> rcases q with j | j
  · simpa [RigidTransform.toHomogeneous] using hasDerivAt_pi.mp (hasDerivAt_pi.mp hR i) j
  · have h := (EuclideanSpace.proj i : Vec3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hp
    simpa [RigidTransform.toHomogeneous, Function.comp_def] using h
  · simpa [RigidTransform.toHomogeneous] using hasDerivAt_const t (0 : ℝ)
  · simpa [RigidTransform.toHomogeneous] using
      hasDerivAt_const t ((1 : Matrix (Fin 1) (Fin 1) ℝ) i j)

/-- Supporting lemma for MLS Lemma 5.10, p. 247: a column curve built from three vector curves has
the column derivatives, `d/dt [a b c] = [ȧ ḃ ċ]`. -/
private theorem hasDerivAt_columns {a b d : ℝ → Vec3} {a' b' d' : Vec3} {t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) (hd : HasDerivAt d d' t) :
    HasDerivAt (fun s => (Matrix.of ![WithLp.ofLp (a s), WithLp.ofLp (b s), WithLp.ofLp (d s)])ᵀ)
      (Matrix.of ![WithLp.ofLp a', WithLp.ofLp b', WithLp.ofLp d'])ᵀ t := by
  have comp : ∀ {f : ℝ → Vec3} {f' : Vec3}, HasDerivAt f f' t → ∀ i : Fin 3,
      HasDerivAt (fun s => f s i) (f' i) t := fun hf i =>
    (EuclideanSpace.proj i : Vec3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hf
  refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
  fin_cases j
  · simpa using comp ha i
  · simpa using comp hb i
  · simpa using comp hd i

/-- Supporting lemma (MLS p. 247, the proof of Lemma 5.10 reads off `Ṙ_oc`): a matrix curve has at
most one derivative, entry by entry. -/
private theorem matrix_hasDerivAt_unique {f : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {A B : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ} (hA : HasDerivAt f A t) (hB : HasDerivAt f B t) :
    A = B := by
  ext i j
  exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) j).unique
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hB i) j)

/-! ### Lemma 5.10 -/

/-- The three frame axes are differentiable on an orthogonal chart (supporting lemma for MLS Lemma
5.10, p. 247, where the proof differentiates `R_oc = [x y z]`). -/
private theorem frame_differentiableAt (hc : IsOrthogonalChartOn c U) {β : Fin 2 → ℝ}
    (hβ : β ∈ U) :
    DifferentiableAt ℝ (frameX c) β ∧ DifferentiableAt ℝ (frameY c) β ∧
      DifferentiableAt ℝ (gaussNormal c) β :=
  ⟨differentiableAt_frameX (hc.contDiffAt hβ) (hc.partialU_ne_zero hβ),
    differentiableAt_frameY (hc.contDiffAt hβ) (hc.partialV_ne_zero hβ),
    differentiableAt_gaussNormal (hc.contDiffAt hβ)
      (cross_partial_ne_zero (hc.orthogonal β hβ) (hc.partialU_ne_zero hβ)
        (hc.partialV_ne_zero hβ))⟩

/-- The rotation of the contact frame along a coordinate curve has the derivative `[ẋ ẏ ż]`,
`ẋ = Dx(α) α̇` and so on (supporting lemma for MLS Lemma 5.10, p. 247). -/
private theorem hasDerivAt_gaussFrame (hc : IsOrthogonalChartOn c U) {α : ℝ → Fin 2 → ℝ}
    {α' : Fin 2 → ℝ} {t : ℝ} (hα : HasDerivAt α α' t) (ht : α t ∈ U) :
    HasDerivAt (fun s => (gaussFrame c (α s)).val)
      (Matrix.of ![WithLp.ofLp (fderiv ℝ (frameX c) (α t) α'),
        WithLp.ofLp (fderiv ℝ (frameY c) (α t) α'),
        WithLp.ofLp (fderiv ℝ (gaussNormal c) (α t) α')])ᵀ t := by
  obtain ⟨hx, hy, hn⟩ := frame_differentiableAt hc ht
  have h := hasDerivAt_columns (hx.hasFDerivAt.comp_hasDerivAt t hα)
    (hy.hasFDerivAt.comp_hasDerivAt t hα) (hn.hasFDerivAt.comp_hasDerivAt t hα)
  have hU : ∀ᶠ s in 𝓝 t, α s ∈ U := hα.continuousAt.preimage_mem_nhds (hc.isOpen.mem_nhds ht)
  have heq : ∀ᶠ s in 𝓝 t, (gaussFrame c (α s)).val = gaussFrameMatrix c (α s) := by
    filter_upwards [hU] with s hs
    exact gaussFrame_val (hc.orthogonal _ hs) (hc.partialU_ne_zero hs) (hc.partialV_ne_zero hs)
  refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
  refine (hasDerivAt_pi.mp (hasDerivAt_pi.mp h i) j).congr_of_eventuallyEq ?_
  filter_upwards [heq] with s hs
  rw [hs]
  rfl

/-- **The contact frame along a coordinate curve has a derivative (MLS p. 246 and Lemma 5.10, p.
247):** for an orthogonal chart on `U` and a coordinate curve `α` with an actual derivative at `t`
and `α(t) ∈ U`, the pose curve `t ↦ g_oc(t) = (c(α(t)), [x y z](α(t)))` has a derivative at `t`. -/
theorem exists_hasDerivAt_contactFrame (hc : IsOrthogonalChartOn c U) {α : ℝ → Fin 2 → ℝ}
    {α' : Fin 2 → ℝ} {t : ℝ} (hα : HasDerivAt α α' t) (ht : α t ∈ U) :
    ∃ D : HomogeneousMatrix, HasDerivAt (fun s => (contactFrame c (α s)).toHomogeneous) D t := by
  have hp : HasDerivAt (fun s => c (α s)) (fderiv ℝ c (α t) α') t :=
    ((hc.contDiffAt ht).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hα
  exact ⟨_, hasDerivAt_toHomogeneous_of (hasDerivAt_gaussFrame hc hα ht) hp⟩

/-- **MLS Lemma 5.10, printed pp. 246–247, eqs. (5.25)–(5.26): the induced velocity of the contact
frame.** For an orthogonal chart `(c, U)` (twice continuously differentiable, injective
differential, `c_u ⟂ c_v`) and a coordinate curve `α` with an actual derivative `α̇` at `t` and
`α(t) ∈ U`, every derivative `D` of the contact frame `g_oc(t) = (c(α(t)), [x y z](α(t)))` gives the
body velocity `V^b_oc = (v_oc, ω_oc)` with `v_oc = (M α̇, 0)` and
`ω_oc = (−(K M α̇)₂, (K M α̇)₁, T M α̇)`, the geometric parameters taken at `α(t)`. -/
theorem bodyVelocity_contactFrame (hc : IsOrthogonalChartOn c U) {α : ℝ → Fin 2 → ℝ}
    {α' : Fin 2 → ℝ} {t : ℝ} (hα : HasDerivAt α α' t) (ht : α t ∈ U) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (contactFrame c (α s)).toHomogeneous) D t) :
    RigidTransform.bodyVelocity (fun s => contactFrame c (α s)) D t hD =
      contactFrameVelocity c (α t) α' := by
  have horth := hc.orthogonal (α t) ht
  have hu := hc.partialU_ne_zero ht
  have hv := hc.partialV_ne_zero ht
  have hu' : ‖partialU c (α t)‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hv' : ‖partialV c (α t)‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  -- the blocks of `D`
  have hA : D.toBlocks₁₁ = (Matrix.of ![WithLp.ofLp (fderiv ℝ (frameX c) (α t) α'),
      WithLp.ofLp (fderiv ℝ (frameY c) (α t) α'),
      WithLp.ofLp (fderiv ℝ (gaussNormal c) (α t) α')])ᵀ :=
    matrix_hasDerivAt_unique (RigidTransform.hasDerivAt_rotation hD)
      (hasDerivAt_gaussFrame hc hα ht)
  have hp : RigidTransform.translationDerivative D = fderiv ℝ c (α t) α' :=
    (RigidTransform.hasDerivAt_translation hD).unique
      (((hc.contDiffAt ht).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hα)
  have hR : (gaussFrame c (α t)).val = gaussFrameMatrix c (α t) := gaussFrame_val horth hu hv
  -- inner products of the frame with `c_u`, `c_v`
  have xu : inner ℝ (frameX c (α t)) (partialU c (α t)) = ‖partialU c (α t)‖ := by
    rw [frameX, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [RCLike.conj_to_real]
    field_simp
  have xv : inner ℝ (frameX c (α t)) (partialV c (α t)) = 0 := by
    rw [frameX, inner_smul_left, show inner ℝ (partialU c (α t)) (partialV c (α t)) = 0 from horth]
    simp
  have yu : inner ℝ (frameY c (α t)) (partialU c (α t)) = 0 := by
    rw [frameY, inner_smul_left, real_inner_comm,
      show inner ℝ (partialU c (α t)) (partialV c (α t)) = 0 from horth]
    simp
  have yv : inner ℝ (frameY c (α t)) (partialV c (α t)) = ‖partialV c (α t)‖ := by
    rw [frameY, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [RCLike.conj_to_real]
    field_simp
  apply Twist.ext
  · -- linear part, (5.25)
    rw [RigidTransform.bodyVelocity_linear, hp]
    change (gaussFrame c (α t))⁻¹.act _ = _
    rw [gaussFrame_inv_act horth hu hv, fderiv_apply_eq]
    apply WithLp.ofLp_injective
    ext i
    fin_cases i <;>
      simp [contactFrameVelocity, metricTensor, inner_add_right, inner_smul_right, xu, xv, yu, yv,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  · -- angular part, (5.26)
    have hskew := Rotation.bodyVelocity_skew (RigidTransform.hasDerivAt_rotation hD)
    simp only [contactFrame_rotation] at hskew
    have hang : (RigidTransform.bodyVelocity (fun s => contactFrame c (α s)) D t hD).angular =
        Vec3.vee ((gaussFrame c (α t)).valᵀ * D.toBlocks₁₁) := by
      simp [RigidTransform.bodyVelocity, Rotation.bodyAngularVelocity,
        Vec3.hatLinearEquiv_symm_apply]
    have e21 : ((gaussFrame c (α t)).valᵀ * D.toBlocks₁₁) 2 1 =
        -((gaussFrame c (α t)).valᵀ * D.toBlocks₁₁) 1 2 := by
      have := congrFun (congrFun hskew 1) 2
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
      linarith
    rw [hang]
    apply WithLp.ofLp_injective
    ext i
    have entry : ∀ (j k : Fin 3), ((gaussFrame c (α t)).valᵀ * D.toBlocks₁₁) j k =
        inner ℝ (![frameX c (α t), frameY c (α t), gaussNormal c (α t)] j)
          (![fderiv ℝ (frameX c) (α t) α', fderiv ℝ (frameY c) (α t) α',
            fderiv ℝ (gaussNormal c) (α t) α'] k) := by
      intro j k
      rw [hR, hA, gaussFrameMatrix, transpose_transpose, EuclideanSpace.inner_eq_star_dotProduct]
      fin_cases j <;> fin_cases k <;>
        simp [Matrix.mul_apply, dotProduct, mul_comm]
    have K := curvatureTensor_eq_frame (c := c) (α := (α t))
    fin_cases i
    · change ((gaussFrame c (α t)).valᵀ * D.toBlocks₁₁) 2 1 = _
      rw [e21, entry]
      simp only [contactFrameVelocity, K, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, fderiv_apply_eq, inner_add_right, inner_smul_right]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, metricTensor]
      field_simp
    · change ((gaussFrame c (α t)).valᵀ * D.toBlocks₁₁) 0 2 = _
      rw [entry]
      simp only [contactFrameVelocity, K, Matrix.cons_val_zero, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, fderiv_apply_eq, inner_add_right, inner_smul_right]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, metricTensor]
      field_simp
    · change ((gaussFrame c (α t)).valᵀ * D.toBlocks₁₁) 1 0 = _
      rw [entry]
      simp only [contactFrameVelocity, torsionForm, Matrix.cons_val_zero, Matrix.cons_val_one,
        fderiv_apply_eq, inner_add_right, inner_smul_right]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, metricTensor]
      field_simp

end Surface
end RoboLean
