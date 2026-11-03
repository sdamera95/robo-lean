import RoboLean.Grasp.ContactBijection

/-!
# The contact set of two whole bodies and the change of chart

MLS Chapter 5, §6.2–§6.3, printed pp. 248–254.

**What MLS states.** "In general, it may take several coordinate charts to completely describe the
surface of the object" (p. 243). "For simplicity, we will restrict ourselves to the case where
motion is contained in a single coordinate chart for each object" (p. 248). "We assume that
`g_of ∈ W ⊂ SE(3)`, where `W` is the set of all relative positions and orientations for which the
two objects are in contact" (p. 249); "Let `W ⊂ SE(3)` be the set of all configurations `g_of` for
which the two objects are in contact" (p. 254). The contact coordinates are `η = (α_f, α_o, ψ)`,
`ψ` the angle between `∂c_f/∂u_f` and `∂c_o/∂u_o` (pp. 248–249); they depend on the charts.

**Formalized.** A surface is described by a family of charts `c i` on domains `U i` (an atlas;
nothing requires the patches to be disjoint or the family to be finite). For two such surfaces:

* the contact parameters of a relative pose `g` are the pairs of chart points, one on each body,
  that `g` brings together with opposite Gauss normals (`atlasContactParameters`), and the contact
  set `W` is the set of poses that have at least one (`atlasContactSet`); it is the union over pairs
  of patches of the contact set of two patches (`atlasContactSet_eq_iUnion`), and for orthogonal
  charts every pose in it is a relative pose `g_of(η)` of some pair of patches, and conversely
  (`mem_atlasContactSet_iff`);
* `W` depends on the atlases only through the set of surface points with their unit normals
  (`orientedPoints`): two atlases of the same oriented surfaces give the same contact set
  (`atlasContactSet_congr`). This is the chart independence of `W` that p. 249 uses.
* **Change of chart.** At a point described by two orthogonal charts with the same Gauss normal,
  the two normalized Gauss frames differ by a rotation `R_z(θ)` about the normal
  (`exists_gaussFrame_eq_mul_zRotation`), so the contact frames differ by `(0, R_z(θ))`. Then the
  relative pose in the new chart at angle `ψ` is the relative pose in the old chart at angle
  `ψ − θ`, for a change of the finger chart (`relativePose_eq_of_finger_frame`) and of the object
  chart (`relativePose_eq_of_object_frame`): the configuration `g_of` is the same, only the contact
  angle is shifted by the angle between the two frames. Along a motion, the hypotheses of Theorem
  5.11 in the new finger chart give those in the old one, with the angle rate shifted by the rate
  of the frame angle, so (5.28) holds in either chart for the same motion
  (`kinematicEquations_of_finger_frame`). The motion is not required to stay in one chart: it may
  be described in any chart that covers its contact point at time `t`.

What is not claimed: that the patches of an atlas cover a closed surface, or a global smooth
structure on `W`. The frame angle `θ` along a motion is a hypothesis with a derivative; its
existence for smooth chart changes is not proved here.
-/

noncomputable section

open Matrix Filter Topology Real

namespace RoboLean
namespace Rolling

open Surface

variable {ι κ : Type*}

/-! ### The contact set of two surfaces given by atlases -/

/-- **The contact parameters of a relative pose (MLS p. 249: the objects "are touching at a
point"; p. 243, several charts per surface):** for a finger atlas `(c_f i, U_f i)` and an object
atlas `(c_o j, U_o j)`, the tuples `(i, α_f, j, α_o)` with `α_f ∈ U_f i`, `α_o ∈ U_o j`, at which
`g` takes the finger point `c_f i (α_f)` to the object point `c_o j (α_o)` and the finger's Gauss
normal there to the opposite of the object's. -/
def atlasContactParameters (cf : ι → (Fin 2 → ℝ) → Vec3) (Uf : ι → Set (Fin 2 → ℝ))
    (co : κ → (Fin 2 → ℝ) → Vec3) (Uo : κ → Set (Fin 2 → ℝ)) (g : RigidTransform) :
    Set (ι × (Fin 2 → ℝ) × κ × (Fin 2 → ℝ)) :=
  {x | x.2.1 ∈ Uf x.1 ∧ x.2.2.2 ∈ Uo x.2.2.1 ∧
    g.applyPoint (cf x.1 x.2.1) = co x.2.2.1 x.2.2.2 ∧
    g.applyVector (gaussNormal (cf x.1) x.2.1) = -gaussNormal (co x.2.2.1) x.2.2.2}

/-- **The contact set `W` of two whole bodies (MLS p. 249, "the set of all relative positions and
orientations for which the two objects are in contact"; p. 254):** the relative poses with at
least one pair of contact parameters. -/
def atlasContactSet (cf : ι → (Fin 2 → ℝ) → Vec3) (Uf : ι → Set (Fin 2 → ℝ))
    (co : κ → (Fin 2 → ℝ) → Vec3) (Uo : κ → Set (Fin 2 → ℝ)) : Set RigidTransform :=
  {g | (atlasContactParameters cf Uf co Uo g).Nonempty}

variable {cf : ι → (Fin 2 → ℝ) → Vec3} {Uf : ι → Set (Fin 2 → ℝ)}
  {co : κ → (Fin 2 → ℝ) → Vec3} {Uo : κ → Set (Fin 2 → ℝ)}

/-- **`W` is the union of the contact sets of pairs of patches (MLS pp. 249, 254):** the contact
set of two atlases is the union over finger patches `i` and object patches `j` of the contact set
of the two patches (`Rolling.contactSet`). -/
theorem atlasContactSet_eq_iUnion :
    atlasContactSet cf Uf co Uo = ⋃ i, ⋃ j, contactSet (cf i) (co j) (Uf i) (Uo j) := by
  ext g
  simp only [atlasContactSet, atlasContactParameters, Set.mem_ofPred_eq, Set.mem_iUnion,
    contactSet]
  constructor
  · rintro ⟨⟨i, αf, j, αo⟩, hf, ho, hp, hn⟩
    exact ⟨i, j, αf, hf, αo, ho, hp, hn⟩
  · rintro ⟨i, j, αf, hf, αo, ho, hp, hn⟩
    exact ⟨⟨i, αf, j, αo⟩, hf, ho, hp, hn⟩

/-- **Every contact configuration of two bodies is a relative pose `g_of(η)` of a pair of patches,
and conversely (MLS p. 249):** for atlases of orthogonal charts, `g ∈ W` exactly when
`g = g_of(η)` for patches `i`, `j` and contact coordinates `η = (α_f, α_o, ψ)` with
`α_f ∈ U_f i`, `α_o ∈ U_o j`. -/
theorem mem_atlasContactSet_iff (hf : ∀ i, IsOrthogonalChartOn (cf i) (Uf i))
    (ho : ∀ j, IsOrthogonalChartOn (co j) (Uo j)) {g : RigidTransform} :
    g ∈ atlasContactSet cf Uf co Uo ↔
      ∃ i j, ∃ η : ContactCoords, η.1 ∈ Uf i ∧ η.2.1 ∈ Uo j ∧
        relativePoseMap (cf i) (co j) η = g := by
  rw [atlasContactSet_eq_iUnion]
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, j, hg⟩
    obtain ⟨η, h1, h2, h3⟩ := exists_relativePoseMap_eq_of_mem_contactSet (hf i) (ho j) hg
    exact ⟨i, j, η, h1, h2, h3⟩
  · rintro ⟨i, j, η, h1, h2, rfl⟩
    exact ⟨i, j, relativePoseMap_mem_contactSet (hf i) (ho j) h1 h2⟩

/-- **The oriented surface of an atlas (MLS pp. 243–245):** the set of pairs (surface point, Gauss
normal) over all patches, `{(c i (α), n_i(α)) | α ∈ U i}`. -/
def orientedPoints (c : ι → (Fin 2 → ℝ) → Vec3) (U : ι → Set (Fin 2 → ℝ)) : Set (Vec3 × Vec3) :=
  ⋃ i, (fun α => (c i α, gaussNormal (c i) α)) '' U i

/-- **`W` from the oriented surfaces (MLS p. 249):** `g ∈ W` exactly when `g` takes some oriented
point `(p, n)` of the finger to `(q, −m)` for some oriented point `(q, m)` of the object. -/
theorem mem_atlasContactSet_iff_orientedPoints {g : RigidTransform} :
    g ∈ atlasContactSet cf Uf co Uo ↔
      ∃ x ∈ orientedPoints cf Uf, ∃ y ∈ orientedPoints co Uo,
        g.applyPoint x.1 = y.1 ∧ g.applyVector x.2 = -y.2 := by
  simp only [atlasContactSet, atlasContactParameters, orientedPoints, Set.mem_iUnion,
    Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨i, αf, j, αo⟩, hf, ho, hp, hn⟩
    exact ⟨_, ⟨i, αf, hf, rfl⟩, _, ⟨j, αo, ho, rfl⟩, hp, hn⟩
  · rintro ⟨_, ⟨i, αf, hf, rfl⟩, _, ⟨j, αo, ho, rfl⟩, hp, hn⟩
    exact ⟨⟨i, αf, j, αo⟩, hf, ho, hp, hn⟩

/-- **The contact set does not depend on the charts (MLS p. 249, `W` is defined by the bodies):**
two finger atlases with the same oriented points and two object atlases with the same oriented
points give the same contact set. -/
theorem atlasContactSet_congr {ι' κ' : Type*} {cf' : ι' → (Fin 2 → ℝ) → Vec3}
    {Uf' : ι' → Set (Fin 2 → ℝ)} {co' : κ' → (Fin 2 → ℝ) → Vec3} {Uo' : κ' → Set (Fin 2 → ℝ)}
    (hf : orientedPoints cf Uf = orientedPoints cf' Uf')
    (ho : orientedPoints co Uo = orientedPoints co' Uo') :
    atlasContactSet cf Uf co Uo = atlasContactSet cf' Uf' co' Uo' := by
  ext g
  rw [mem_atlasContactSet_iff_orientedPoints, mem_atlasContactSet_iff_orientedPoints, hf, ho]

/-! ### Change of chart -/

/-- A point of the unit circle has an angle (supporting lemma for the frame change, MLS p. 248,
the contact angle). -/
private theorem exists_angle_of_sq_add_sq_eq_one' (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ t : ℝ, Real.cos t = c ∧ Real.sin t = s := by
  let z : ℂ := ⟨c, s⟩
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def]
    change Real.sqrt (c * c + s * s) = 1
    rw [show c * c + s * s = 1 by simpa only [pow_two] using hcs, Real.sqrt_one]
  have hz : z ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hn
    norm_num at hn
  refine ⟨z.arg, ?_, ?_⟩
  · simpa only [hn, div_one] using Complex.cos_arg hz
  · simpa only [hn, div_one] using Complex.sin_arg z

/-- **A rotation fixing the `z`-axis is a rotation about it (MLS Example 2.4, p. 53, used for the
contact angle of p. 248):** if `R e_z = e_z` then `R = R_z(θ)` for some angle `θ`. -/
theorem exists_eq_zRotation_of_act_axisZ (R : Rotation)
    (hz : R.act (WithLp.toLp 2 ![0, 0, 1]) = WithLp.toLp 2 ![0, 0, 1]) :
    ∃ θ : ℝ, R = Rotation.zRotation θ := by
  set Q := R.val with hQ
  have hcol : ∀ i, Q i 2 = (![0, 0, 1] : Fin 3 → ℝ) i := by
    intro i
    have := congrArg (fun v : Vec3 => v i) hz
    simpa [Rotation.act_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Q] using this
  have h02 : Q 0 2 = 0 := by simpa using hcol 0
  have h12 : Q 1 2 = 0 := by simpa using hcol 1
  have h22 : Q 2 2 = 1 := by simpa using hcol 2
  have hO1 := R.mul_transpose
  have hO2 := R.transpose_mul
  have hdet := R.det_eq_one
  rw [← hQ] at hO1 hO2 hdet
  have r22 := congrFun (congrFun hO1 2) 2
  have c00 := congrFun (congrFun hO2 0) 0
  have c01 := congrFun (congrFun hO2 0) 1
  have c11 := congrFun (congrFun hO2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_succ, h22] at r22 c00 c01 c11
  rw [Matrix.det_fin_three, h02, h12, h22] at hdet
  have h20 : Q 2 0 = 0 := by nlinarith [sq_nonneg (Q 2 0), sq_nonneg (Q 2 1)]
  have h21 : Q 2 1 = 0 := by nlinarith [sq_nonneg (Q 2 0), sq_nonneg (Q 2 1)]
  rw [h20] at c00
  rw [h20, h21] at c01
  rw [h21] at c11
  have hsq : (Q 0 0 - Q 1 1) ^ 2 + (Q 0 1 + Q 1 0) ^ 2 = 0 := by
    linear_combination c00 + c11 - 2 * hdet
  obtain ⟨e1, e2⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hsq
  have had : Q 1 1 = Q 0 0 := by linarith [(pow_eq_zero_iff two_ne_zero).mp e1]
  have hbc : Q 0 1 = -Q 1 0 := by linarith [(pow_eq_zero_iff two_ne_zero).mp e2]
  obtain ⟨θ, hcos, hsin⟩ := exists_angle_of_sq_add_sq_eq_one' (Q 0 0) (Q 1 0)
    (by linear_combination c00)
  refine ⟨θ, Subtype.ext ?_⟩
  change Q = (Rotation.zRotation θ).val
  rw [Rotation.zRotation_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hcos, hsin, h02, h12, h22, h20, h21, had, hbc]

variable {c c' : (Fin 2 → ℝ) → Vec3} {α β : Fin 2 → ℝ}

/-- **Two orthogonal charts with the same normal at a point have Gauss frames that differ by a
rotation about the normal (MLS eq. (5.22), p. 245, and the contact angle of p. 248):** if
`c_u, c_v ≠ 0` with `c_u ⟂ c_v` at `α`, the same for `c'` at `β`, and the Gauss normals agree,
`n'(β) = n(α)`, then `[x' y' n'] = [x y n] R_z(θ)` for some angle `θ`. -/
theorem exists_gaussFrame_eq_mul_zRotation (h : IsOrthogonalAt c α) (hu : partialU c α ≠ 0)
    (hv : partialV c α ≠ 0) (h' : IsOrthogonalAt c' β) (hu' : partialU c' β ≠ 0)
    (hv' : partialV c' β ≠ 0) (hn : gaussNormal c' β = gaussNormal c α) :
    ∃ θ : ℝ, gaussFrame c' β = gaussFrame c α * Rotation.zRotation θ := by
  obtain ⟨θ, hθ⟩ := exists_eq_zRotation_of_act_axisZ ((gaussFrame c α)⁻¹ * gaussFrame c' β) (by
    rw [Rotation.act_mul, gaussFrame_act_axisZ h' hu' hv', hn, ← gaussFrame_act_axisZ h hu hv,
      Rotation.inv_act_act])
  exact ⟨θ, by rw [← hθ, mul_inv_cancel_left]⟩

/-- **The contact frames of two charts at a common point (MLS p. 249, the contact frames `C_o`,
`C_f`):** if `c'(β) = c(α)` and `[x' y' n'] = [x y n] R_z(θ)`, then
`g_{oc'}(β) = g_{oc}(α) (0, R_z(θ))`. -/
theorem contactFrame_eq_mul_zRotation {θ : ℝ} (hp : c' β = c α)
    (hR : gaussFrame c' β = gaussFrame c α * Rotation.zRotation θ) :
    contactFrame c' β = contactFrame c α * ⟨Rotation.zRotation θ, 0⟩ := by
  ext1
  · simp [contactFrame, hR]
  · simp [contactFrame, hp]

/-- The contact rotation turned by `R_z(θ)⁻¹` on the right (supporting lemma for MLS eq. (5.34),
p. 251): `diag(R_ψ, −1) R_z(θ)⁻¹ = diag(R_{ψ−θ}, −1)`. -/
private theorem contactOffset_mul_inv_zRotation (ψ θ : ℝ) :
    contactOffset ψ * (⟨Rotation.zRotation θ, 0⟩ : RigidTransform)⁻¹ = contactOffset (ψ - θ) := by
  ext1
  · apply Subtype.ext
    change contactRotationMatrix ψ * ((Rotation.zRotation θ).val)ᵀ = contactRotationMatrix (ψ - θ)
    rw [Rotation.zRotation_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [contactRotationMatrix, Matrix.mul_apply, Fin.sum_univ_succ, cos_sub, sin_sub] <;> ring
  · simp [contactOffset]

/-- The contact rotation turned by `R_z(θ)` on the left (supporting lemma for MLS eq. (5.34),
p. 251): `R_z(θ) diag(R_ψ, −1) = diag(R_{ψ−θ}, −1)`. -/
private theorem zRotation_mul_contactOffset (ψ θ : ℝ) :
    (⟨Rotation.zRotation θ, 0⟩ : RigidTransform) * contactOffset ψ = contactOffset (ψ - θ) := by
  ext1
  · apply Subtype.ext
    change (Rotation.zRotation θ).val * contactRotationMatrix ψ = contactRotationMatrix (ψ - θ)
    rw [Rotation.zRotation_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [contactRotationMatrix, Matrix.mul_apply, Fin.sum_univ_succ, cos_sub, sin_sub] <;> ring
  · simp [contactOffset]

/-- **Change of the finger chart (MLS pp. 248–249):** if the finger's contact frame in the chart
`c'_f` at `β` is the contact frame in the chart `c_f` at `α` turned by `R_z(θ)`, then the relative
pose of the new contact coordinates `(β, α_o, ψ)` is the relative pose of `(α, α_o, ψ − θ)`. -/
theorem relativePose_eq_of_finger_frame {cf cf' co : (Fin 2 → ℝ) → Vec3} {αf βf αo : Fin 2 → ℝ}
    {θ : ℝ} (h : contactFrame cf' βf = contactFrame cf αf * ⟨Rotation.zRotation θ, 0⟩) (ψ : ℝ) :
    relativePose cf' co βf αo ψ = relativePose cf co αf αo (ψ - θ) := by
  rw [relativePose, relativePose, h, _root_.mul_inv_rev, ← mul_assoc, mul_assoc (contactFrame co αo),
    contactOffset_mul_inv_zRotation]

/-- **Change of the object chart (MLS pp. 248–249):** if the object's contact frame in the chart
`c'_o` at `β` is the contact frame in the chart `c_o` at `α` turned by `R_z(θ)`, then the relative
pose of the new contact coordinates `(α_f, β, ψ)` is the relative pose of `(α_f, α, ψ − θ)`. -/
theorem relativePose_eq_of_object_frame {cf co co' : (Fin 2 → ℝ) → Vec3} {αf αo βo : Fin 2 → ℝ}
    {θ : ℝ} (h : contactFrame co' βo = contactFrame co αo * ⟨Rotation.zRotation θ, 0⟩) (ψ : ℝ) :
    relativePose cf co' αf βo ψ = relativePose cf co αf αo (ψ - θ) := by
  rw [relativePose, relativePose, h, mul_assoc (contactFrame co αo), zRotation_mul_contactOffset]

/-- **MLS Theorem 5.11 (p. 250) transfers across a change of the finger chart.** Let a motion be
described in the finger chart `c'_f` (a pose curve `g` agreeing near `t` with
`g_of(β(s), α_o(s), ψ(s))`), and let a second orthogonal chart `(c_f, U_f)` cover the same contact
points near `t`, with coordinates `α_f(s) ∈ U_f` whose contact frames differ by `R_z(θ(s))`
(`g_{fc'_f}(β(s)) = g_{fc_f}(α_f(s)) (0, R_z(θ(s)))`). If `α_f`, `α_o`, `ψ` and `θ` have
derivatives at `t` and `K_f + K̃_o` is invertible at `(α_f(t), α_o(t), ψ(t) − θ(t))` in the chart
`c_f`, then the same motion satisfies (5.28) in the chart `c_f`, with angle `ψ − θ` and angle rate
`ψ̇ − θ̇`. -/
theorem kinematicEquations_of_finger_frame {cf cf' co : (Fin 2 → ℝ) → Vec3}
    {Uf Uo : Set (Fin 2 → ℝ)} (hf : IsOrthogonalChartOn cf Uf) (ho : IsOrthogonalChartOn co Uo)
    {αf βf αo : ℝ → Fin 2 → ℝ} {ψ θ : ℝ → ℝ} {αf' αo' : Fin 2 → ℝ} {ψ' θ' t : ℝ}
    (hαf : HasDerivAt αf αf' t) (hαo : HasDerivAt αo αo' t) (hψ : HasDerivAt ψ ψ' t)
    (hθ : HasDerivAt θ θ' t) (hft : αf t ∈ Uf) (hot : αo t ∈ Uo)
    (hframe : ∀ᶠ s in 𝓝 t,
      contactFrame cf' (βf s) = contactFrame cf (αf s) * ⟨Rotation.zRotation (θ s), 0⟩)
    (hX : IsUnit (relativeCurvature (curvatureTensor cf (αf t)) (curvatureTensor co (αo t))
      (ψ t - θ t)).det) {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t, g s = relativePose cf' co (βf s) (αo s) (ψ s)) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    KinematicEquations (metricTensor cf (αf t)) (curvatureTensor cf (αf t))
      (metricTensor co (αo t)) (curvatureTensor co (αo t)) (torsionForm cf (αf t))
      (torsionForm co (αo t)) (ψ t - θ t) αf' αo' (ψ' - θ')
      (Twist.adjoint (contactFrame cf (αf t))⁻¹ (RigidTransform.bodyVelocity g D t hD)) := by
  have hg' : ∀ᶠ s in 𝓝 t, g s = relativePose cf co (αf s) (αo s) (ψ s - θ s) := by
    filter_upwards [hg, hframe] with s h1 h2
    rw [h1, relativePose_eq_of_finger_frame h2]
  exact kinematicEquations_of_hasDerivAt (ψ := fun s => ψ s - θ s) hf ho hαf hαo (hψ.sub hθ) hft
    hot hX hg' hD

end Rolling
end RoboLean
