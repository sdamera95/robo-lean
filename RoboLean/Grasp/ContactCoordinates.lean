import RoboLean.Grasp.ContactFrameVelocity

/-!
# Contact coordinates and the relative pose of two surfaces in contact

MLS Chapter 5, §6.2 "Contact kinematics", printed pp. 248–251, with eqs. (5.27) and (5.34).

**What MLS states.** Two objects with surfaces `S_o` and `S_f` touch at a point; `(c_o, U_o)` and
`(c_f, U_f)` are orthogonal charts, `α_o`, `α_f` the local coordinates of the contact point, and
"Let `ψ` be the angle of contact, defined as the angle between the tangent vectors `∂c_f/∂u_f` and
`∂c_o/∂u_o`. We choose the sign of `ψ` so that a rotation of `∂c_o/∂u_o` through an angle `ψ` around
the outward normal of `S_o` aligns `∂c_o/∂u_o` with `∂c_f/∂u_f`" (pp. 248–249). "`η = (α_f, α_o, ψ)`
[are] the contact coordinates"; `g_of ∈ SE(3)` is the relative pose of `S_f` with respect to `S_o`
(p. 249). The contact frames `C_o`, `C_f` coincide with the normalized Gauss frames at the contact
point (p. 249). `V^b_{l_o l_f} = Ad⁻¹_{g_{f l_f}} V_of`, in components
`[R_{f l_f}ᵀ v_of − R_{f l_f}ᵀ p̂_o ω_of; R_{f l_f}ᵀ ω_of]` (5.27, p. 250).
`R_ψ = [[cos ψ, −sin ψ], [−sin ψ, −cos ψ]]`, `K̃_o = R_ψ K_o R_ψ`, "`R_ψ` is the orientation of the
`x`- and `y`-axes of `C_f` relative to the `x`- and `y`-axes of `C_o`", and `K_f + K̃_o` is "the
relative curvature form" (p. 250). In the proof of Theorem 5.11, `p_{c_o c_f} = 0`,
`R_{c_o c_f} = [[R_ψ, 0], [0, 1]]`, hence `v_{c_o c_f} = 0` and `ω_{c_o c_f} = (0, 0, ψ̇)` (5.34, p.
251).

**Formalized and the conventions fixed here.**

* `angleMatrix ψ` is `R_ψ` as printed: symmetric, `R_ψ² = I`, `det R_ψ = −1` (a reflection).
* The contact rotation `R_{c_o c_f}` is `diag(R_ψ, −1)` (`contactRotation`), a proper rotation. The
  printed (5.34) has third diagonal entry `+1`, which gives determinant `−1` and is not a rotation;
  with `−1` the two Gauss normals are opposed, `n_f ↦ −n_o`, and `ω_{c_o c_f} = (0, 0, ψ̇)` holds
  (`bodyVelocity_contactOffset`). This is the convention under which Theorem 5.11 (5.28) holds.
* The relative pose is `g_of(η) = g_{o c_o}(α_o) · (0, R_{c_o c_f}(ψ)) · g_{f c_f}(α_f)⁻¹`
  (`relativePose`), not printed by the book: the contact points coincide
  (`relativePose_applyPoint`), the normals are opposed (`relativePose_applyVector_gaussNormal`), and
  the first finger axis is `x_f ↦ cos ψ x_o − sin ψ y_o` (`relativePose_applyVector_frameX`), so `ψ`
  is the right-handed angle from `x_o` to `x_f` about the finger normal `−n_o`. This is the
  orientation the matrix `R_ψ` of p. 250 encodes; the prose rule of p. 248 ("a rotation ... around
  the outward normal of `S_o`") gives the opposite sense under the right-hand rule.
* (5.27) holds with the finger's contact point `p_{f l_f} = c_f(α_f)` in the cross product
  (`adjoint_inv_contactFrame`), the translation of `g_{f l_f}`; the printed `p̂_o` is not used.
* The bridge to the contact frames of MLS §2, whose `z`-axis is the inward normal (p. 214):
  `inwardContactFrame c α = g_oc(α) · (0, diag(1, −1, −1))` keeps the origin and `x`, and has
  `z = −n`; when `n` is outward (`IsOutwardNormal`) its `z`-axis points into the body
  (`fderiv_inwardContactFrame_axisZ_neg`). The finger's Gauss frame at the contact is that frame
  turned by `ψ` about its `z`-axis:
  `g_{o c_o} · (0, R_{c_o c_f}(ψ)) = inwardContactFrame · (0, R_z(ψ))`
  (`contactFrame_mul_contactOffset`).
-/

noncomputable section

open Matrix Filter Topology Real

namespace RoboLean

namespace Surface

variable {c : (Fin 2 → ℝ) → Vec3} {α : Fin 2 → ℝ}

/-- **The first axis of the normalized Gauss frame (MLS eq. (5.22), p. 245):** the rotation
`[x y n]` takes `e_x` to `x = c_u/‖c_u‖`, for an orthogonal chart with `c_u, c_v ≠ 0`. -/
theorem gaussFrame_act_axisX (h : IsOrthogonalAt c α) (hu : partialU c α ≠ 0)
    (hv : partialV c α ≠ 0) : (gaussFrame c α).act (WithLp.toLp 2 ![1, 0, 0]) = frameX c α := by
  apply WithLp.ofLp_injective
  ext i
  rw [Rotation.act_apply, gaussFrame_val h hu hv, gaussFrameMatrix]
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- **The second axis of the normalized Gauss frame (MLS eq. (5.22), p. 245):** the rotation
`[x y n]` takes `e_y` to `y = c_v/‖c_v‖`, for an orthogonal chart with `c_u, c_v ≠ 0`. -/
theorem gaussFrame_act_axisY (h : IsOrthogonalAt c α) (hu : partialU c α ≠ 0)
    (hv : partialV c α ≠ 0) : (gaussFrame c α).act (WithLp.toLp 2 ![0, 1, 0]) = frameY c α := by
  apply WithLp.ofLp_injective
  ext i
  rw [Rotation.act_apply, gaussFrame_val h hu hv, gaussFrameMatrix]
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- **The third axis of the normalized Gauss frame (MLS eq. (5.22), p. 245):** the rotation
`[x y n]` takes `e_z` to the Gauss normal `n`, for an orthogonal chart with `c_u, c_v ≠ 0`. -/
theorem gaussFrame_act_axisZ (h : IsOrthogonalAt c α) (hu : partialU c α ≠ 0)
    (hv : partialV c α ≠ 0) :
    (gaussFrame c α).act (WithLp.toLp 2 ![0, 0, 1]) = gaussNormal c α := by
  apply WithLp.ofLp_injective
  ext i
  rw [Rotation.act_apply, gaussFrame_val h hu hv, gaussFrameMatrix]
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end Surface

namespace Rolling

open Surface

/-! ### The angle matrix and the relative curvature form -/

/-- **The matrix `R_ψ` of MLS p. 250:** `R_ψ = [[cos ψ, −sin ψ], [−sin ψ, −cos ψ]]`, "the
orientation of the `x`- and `y`-axes of `C_f` relative to the `x`- and `y`-axes of `C_o`", as
printed. -/
def angleMatrix (ψ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![cos ψ, -sin ψ; -sin ψ, -cos ψ]

/-- **`R_ψ` is symmetric (MLS p. 250),** so `R_ψ K_o R_ψ` is the `R_ψ K_o R_ψᵀ` of Proposition 5.12,
p. 254. -/
theorem angleMatrix_transpose (ψ : ℝ) : (angleMatrix ψ)ᵀ = angleMatrix ψ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [angleMatrix]

/-- **`R_ψ² = I` (MLS p. 250):** `R_ψ` is its own inverse. -/
theorem angleMatrix_mul_self (ψ : ℝ) : angleMatrix ψ * angleMatrix ψ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [angleMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [sin_sq_add_cos_sq ψ]

/-- **`R_ψ` is a reflection (MLS p. 250):** `det R_ψ = −1`. -/
theorem det_angleMatrix (ψ : ℝ) : (angleMatrix ψ).det = -1 := by
  rw [angleMatrix, Matrix.det_fin_two_of]
  nlinarith [sin_sq_add_cos_sq ψ]

/-- **`K̃_o = R_ψ K_o R_ψ` (MLS p. 250):** "the curvature of `O` at the point of contact relative to
the `x`- and `y`-axes of `C_f`". -/
def rotatedCurvature (Ko : Matrix (Fin 2) (Fin 2) ℝ) (ψ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  angleMatrix ψ * Ko * angleMatrix ψ

/-- **The relative curvature form `K_f + K̃_o` (MLS p. 250).** -/
def relativeCurvature (Kf Ko : Matrix (Fin 2) (Fin 2) ℝ) (ψ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Kf + rotatedCurvature Ko ψ

/-! ### The contact rotation `R_{c_o c_f}` -/

/-- **The orientation of `C_f` relative to `C_o`, `R_{c_o c_f} = diag(R_ψ, −1)` (MLS eq. (5.34), p.
251, with the third diagonal entry `−1`):** the printed `+1` gives determinant `−1`; with `−1` the
matrix is a proper rotation and takes the normal of `C_f` to the opposite of the normal of `C_o`. -/
def contactRotationMatrix (ψ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos ψ, -sin ψ, 0; -sin ψ, -cos ψ, 0; 0, 0, -1]

/-- **`diag(R_ψ, −1)` is a proper rotation (MLS eq. (5.34), p. 251, with the entry `−1`).** -/
theorem contactRotationMatrix_mem (ψ : ℝ) :
    contactRotationMatrix ψ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  refine Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [contactRotationMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      nlinarith [sin_sq_add_cos_sq ψ]
  · rw [contactRotationMatrix, Matrix.det_fin_three]
    simp
    nlinarith [sin_sq_add_cos_sq ψ]

/-- **The contact rotation `R_{c_o c_f} = diag(R_ψ, −1)` as an element of `SO(3)` (MLS eq. (5.34),
p. 251, with the entry `−1`).** -/
def contactRotation (ψ : ℝ) : Rotation := ⟨contactRotationMatrix ψ, contactRotationMatrix_mem ψ⟩

/-- **The pose of `C_f` relative to `C_o`, `g_{c_o c_f} = (0, R_{c_o c_f})` (MLS eq. (5.34), p.
251):** the two contact frames share their origin, `p_{c_o c_f} = 0`. -/
def contactOffset (ψ : ℝ) : RigidTransform := ⟨contactRotation ψ, 0⟩

/-- The derivative of the contact rotation along an angle curve (supporting lemma for MLS eq.
(5.34), p. 251). -/
private theorem hasDerivAt_contactRotationMatrix {ψ : ℝ → ℝ} {ψ' t : ℝ}
    (hψ : HasDerivAt ψ ψ' t) :
    HasDerivAt (fun s => (contactOffset (ψ s)).rotation.val)
      (ψ' • !![-sin (ψ t), -cos (ψ t), 0; -cos (ψ t), sin (ψ t), 0; 0, 0, 0]) t := by
  have hc : HasDerivAt (fun s => cos (ψ s)) (-sin (ψ t) * ψ') t :=
    (hasDerivAt_cos (ψ t)).comp t hψ
  have hcn : HasDerivAt (fun s => -cos (ψ s)) (-(-sin (ψ t) * ψ')) t := hc.neg
  have hsn : HasDerivAt (fun s => -sin (ψ s)) (-(cos (ψ t) * ψ')) t :=
    ((hasDerivAt_sin (ψ t)).comp t hψ).neg
  refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [contactOffset, contactRotation, contactRotationMatrix]
  all_goals first
    | exact hasDerivAt_const t _
    | (convert hc using 1; ring1)
    | (convert hcn using 1; ring1)
    | (convert hsn using 1; ring1)

/-- The origin of `C_f` stays at the origin of `C_o` (supporting lemma for MLS eq. (5.34), p. 251,
`p_{c_o c_f} = 0`). -/
private theorem hasDerivAt_contactOffset_translation (ψ : ℝ → ℝ) (t : ℝ) :
    HasDerivAt (fun s => (contactOffset (ψ s)).translation) (0 : Vec3) t := by
  change HasDerivAt (fun _ => (0 : Vec3)) 0 t
  exact hasDerivAt_const t (0 : Vec3)

/-- **The contact offset along an angle curve has a derivative (MLS eq. (5.34), p. 251).** -/
theorem exists_hasDerivAt_contactOffset {ψ : ℝ → ℝ} {ψ' t : ℝ} (hψ : HasDerivAt ψ ψ' t) :
    ∃ D : HomogeneousMatrix, HasDerivAt (fun s => (contactOffset (ψ s)).toHomogeneous) D t :=
  ⟨_, Surface.hasDerivAt_toHomogeneous_of (hasDerivAt_contactRotationMatrix hψ)
    (hasDerivAt_contactOffset_translation ψ t)⟩

/-- **MLS eq. (5.34), p. 251: `v_{c_o c_f} = 0` and `ω_{c_o c_f} = (0, 0, ψ̇)`**, the body velocity
of `g_{c_o c_f} = (0, diag(R_ψ, −1))` along an angle curve `ψ` with an actual derivative `ψ̇` at
`t`, for every derivative `D` of the pose curve. -/
theorem bodyVelocity_contactOffset {ψ : ℝ → ℝ} {ψ' t : ℝ} (hψ : HasDerivAt ψ ψ' t)
    {D : HomogeneousMatrix} (hD : HasDerivAt (fun s => (contactOffset (ψ s)).toHomogeneous) D t) :
    RigidTransform.bodyVelocity (fun s => contactOffset (ψ s)) D t hD =
      ⟨0, WithLp.toLp 2 ![0, 0, ψ']⟩ := by
  have hA : D.toBlocks₁₁ =
      ψ' • !![-sin (ψ t), -cos (ψ t), 0; -cos (ψ t), sin (ψ t), 0; 0, 0, 0] := by
    ext i j
    exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp (RigidTransform.hasDerivAt_rotation hD) i) j).unique
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp (hasDerivAt_contactRotationMatrix hψ) i) j)
  have hp : RigidTransform.translationDerivative D = 0 :=
    (RigidTransform.hasDerivAt_translation hD).unique (hasDerivAt_contactOffset_translation ψ t)
  apply Twist.ext
  · rw [RigidTransform.bodyVelocity_linear, hp, map_zero]
  · have hang : (RigidTransform.bodyVelocity (fun s => contactOffset (ψ s)) D t hD).angular =
        Vec3.vee ((contactOffset (ψ t)).rotation.valᵀ * D.toBlocks₁₁) := by
      simp [RigidTransform.bodyVelocity, Rotation.bodyAngularVelocity,
        Vec3.hatLinearEquiv_symm_apply]
    rw [hang, hA]
    apply WithLp.ofLp_injective
    ext i
    fin_cases i <;>
      simp [Vec3.vee, contactOffset, contactRotation, contactRotationMatrix, Matrix.mul_apply,
        Fin.sum_univ_succ]
    all_goals first
      | ring1
      | linear_combination ψ' * sin_sq_add_cos_sq (ψ t)

/-! ### The relative pose of the two objects -/

/-- **The relative pose `g_of` of the finger frame `F` with respect to the object frame `O` in terms
of the contact coordinates `η = (α_f, α_o, ψ)` (MLS p. 249):**
`g_of(η) = g_{o c_o}(α_o) · (0, diag(R_ψ, −1)) · g_{f c_f}(α_f)⁻¹`, assembled from the contact
frames of p. 249 and eq. (5.34), p. 251 (with the entry `−1`); the book does not print this formula.
-/
def relativePose (cf co : (Fin 2 → ℝ) → Vec3) (αf αo : Fin 2 → ℝ) (ψ : ℝ) : RigidTransform :=
  contactFrame co αo * contactOffset ψ * (contactFrame cf αf)⁻¹

/-- **The contact points coincide (MLS p. 248: the surfaces "are touching at a point"):** `g_of(η)`
takes the finger's contact point `c_f(α_f)` (in `F`) to the object's contact point `c_o(α_o)` (in
`O`). -/
theorem relativePose_applyPoint (cf co : (Fin 2 → ℝ) → Vec3) (αf αo : Fin 2 → ℝ) (ψ : ℝ) :
    (relativePose cf co αf αo ψ).applyPoint (cf αf) = co αo := by
  simp [relativePose, RigidTransform.applyPoint, contactOffset, contactFrame]

/-- The contact rotation takes `e_z` to `−e_z` (MLS eq. (5.34), p. 251, with the entry `−1`). -/
private theorem contactRotation_act_axisZ (ψ : ℝ) :
    (contactRotation ψ).act (WithLp.toLp 2 ![0, 0, 1]) = -WithLp.toLp 2 ![0, 0, 1] := by
  apply WithLp.ofLp_injective
  ext i
  rw [Rotation.act_apply]
  fin_cases i <;> simp [contactRotation, contactRotationMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

/-- The contact rotation takes `e_x` to `cos ψ e_x − sin ψ e_y` (MLS p. 250: `R_ψ` is the
orientation of the axes of `C_f` relative to `C_o`). -/
private theorem contactRotation_act_axisX (ψ : ℝ) :
    (contactRotation ψ).act (WithLp.toLp 2 ![1, 0, 0]) =
      cos ψ • WithLp.toLp 2 ![1, 0, 0] - sin ψ • WithLp.toLp 2 ![0, 1, 0] := by
  apply WithLp.ofLp_injective
  ext i
  rw [Rotation.act_apply]
  fin_cases i <;> simp [contactRotation, contactRotationMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

/-- **The normals at the contact are opposed (MLS p. 249, and eq. (5.34), p. 251, with the entry
`−1`):** for charts orthogonal at the contact coordinates with nonzero partials, `g_of(η)` takes the
finger's Gauss normal `n_f` to `−n_o`. -/
theorem relativePose_applyVector_gaussNormal {cf co : (Fin 2 → ℝ) → Vec3} {αf αo : Fin 2 → ℝ}
    (hf : IsOrthogonalAt cf αf) (hfu : partialU cf αf ≠ 0) (hfv : partialV cf αf ≠ 0)
    (ho : IsOrthogonalAt co αo) (hou : partialU co αo ≠ 0) (hov : partialV co αo ≠ 0) (ψ : ℝ) :
    (relativePose cf co αf αo ψ).applyVector (gaussNormal cf αf) = -gaussNormal co αo := by
  rw [← gaussFrame_act_axisZ hf hfu hfv, ← gaussFrame_act_axisZ ho hou hov]
  simp only [relativePose, RigidTransform.applyVector, RigidTransform.mul_rotation,
    RigidTransform.inv_rotation, Rotation.act_mul, contactFrame_rotation, Rotation.inv_act_act]
  rw [show (contactOffset ψ).rotation = contactRotation ψ from rfl, contactRotation_act_axisZ,
    map_neg]

/-- **The sign of the contact angle (MLS p. 250: "`R_ψ` is the orientation of the `x`- and `y`-axes
of `C_f` relative to the `x`- and `y`-axes of `C_o`"):** for charts orthogonal at the contact
coordinates with nonzero partials, `g_of(η)` takes the finger axis `x_f = ∂c_f/∂u_f/‖∂c_f/∂u_f‖` to
`cos ψ x_o − sin ψ y_o`, the rotation of `x_o` by `ψ` about the finger normal `−n_o`. -/
theorem relativePose_applyVector_frameX {cf co : (Fin 2 → ℝ) → Vec3} {αf αo : Fin 2 → ℝ}
    (hf : IsOrthogonalAt cf αf) (hfu : partialU cf αf ≠ 0) (hfv : partialV cf αf ≠ 0)
    (ho : IsOrthogonalAt co αo) (hou : partialU co αo ≠ 0) (hov : partialV co αo ≠ 0) (ψ : ℝ) :
    (relativePose cf co αf αo ψ).applyVector (frameX cf αf) =
      cos ψ • frameX co αo - sin ψ • frameY co αo := by
  rw [← gaussFrame_act_axisX hf hfu hfv, ← gaussFrame_act_axisX ho hou hov,
    ← gaussFrame_act_axisY ho hou hov]
  simp only [relativePose, RigidTransform.applyVector, RigidTransform.mul_rotation,
    RigidTransform.inv_rotation, Rotation.act_mul, contactFrame_rotation, Rotation.inv_act_act]
  rw [show (contactOffset ψ).rotation = contactRotation ψ from rfl, contactRotation_act_axisX,
    map_sub, map_smul, map_smul]

/-- **MLS eq. (5.27), p. 250, with the finger's contact point:** for the local frame
`g_{f l_f} = g_{f c_f}(α_f)` frozen at the contact,
`Ad⁻¹_{g_{f l_f}} V = (R_{f l_f}ᵀ (v − p_{f l_f} × ω), R_{f l_f}ᵀ ω)` with `p_{f l_f} = c_f(α_f)`
the translation of `g_{f l_f}` (the printed formula writes `p̂_o`). -/
theorem adjoint_inv_contactFrame (cf : (Fin 2 → ℝ) → Vec3) (αf : Fin 2 → ℝ) (V : Twist) :
    Twist.adjoint (contactFrame cf αf)⁻¹ V =
      ⟨(gaussFrame cf αf)⁻¹.act (V.linear - Vec3.cross (cf αf) V.angular),
        (gaussFrame cf αf)⁻¹.act V.angular⟩ := by
  rw [Twist.adjoint_inv]
  rfl

/-! ### The inward-normal contact frame of MLS §2 -/

/-- **The rotation by `π` about the `x`-axis, `diag(1, −1, −1)`:** the fixed rotation between a
normalized Gauss frame (`z` along `n`, MLS p. 245) and a contact frame of MLS §2 (`z` along the
inward normal, p. 214; p. 246, footnote 2). -/
def inwardFlip : Rotation :=
  ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by
    refine Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩
    · rw [Matrix.mem_orthogonalGroup_iff']
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
    · simp [Matrix.det_fin_three]⟩

/-- **A contact frame in the convention of MLS §2 built from the normalized Gauss frame (MLS p. 214,
"the `z`-axis ... pointing into the object"; p. 246, footnote 2):**
`g_oc(α) · (0, diag(1, −1, −1))`, with origin `c(α)`, `x`-axis `x = c_u/‖c_u‖`, `y`-axis `−y` and
`z`-axis `−n`. -/
def inwardContactFrame (c : (Fin 2 → ℝ) → Vec3) (α : Fin 2 → ℝ) : RigidTransform :=
  contactFrame c α * ⟨inwardFlip, 0⟩

/-- The origin of the inward-normal contact frame is the contact point `c(α)` (MLS p. 214). -/
theorem inwardContactFrame_translation (c : (Fin 2 → ℝ) → Vec3) (α : Fin 2 → ℝ) :
    (inwardContactFrame c α).translation = c α := by
  simp [inwardContactFrame]

/-- **The `z`-axis of the inward-normal contact frame is `−n` (MLS p. 214 and p. 246, footnote 2)**,
for an orthogonal chart with `c_u, c_v ≠ 0`. -/
theorem inwardContactFrame_axisZ {c : (Fin 2 → ℝ) → Vec3} {α : Fin 2 → ℝ}
    (h : IsOrthogonalAt c α) (hu : partialU c α ≠ 0) (hv : partialV c α ≠ 0) :
    (inwardContactFrame c α).rotation.act (WithLp.toLp 2 ![0, 0, 1]) = -gaussNormal c α := by
  have hflip : inwardFlip.act (WithLp.toLp 2 ![0, 0, 1]) = -WithLp.toLp 2 ![0, 0, 1] := by
    apply WithLp.ofLp_injective
    ext i
    rw [Rotation.act_apply]
    fin_cases i <;> simp [inwardFlip, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  simp only [inwardContactFrame, RigidTransform.mul_rotation, Rotation.act_mul,
    contactFrame_rotation, hflip, map_neg]
  rw [gaussFrame_act_axisZ h hu hv]

/-- **The `x`-axis of the inward-normal contact frame is `x = c_u/‖c_u‖` (MLS p. 245)**, for an
orthogonal chart with `c_u, c_v ≠ 0`. -/
theorem inwardContactFrame_axisX {c : (Fin 2 → ℝ) → Vec3} {α : Fin 2 → ℝ}
    (h : IsOrthogonalAt c α) (hu : partialU c α ≠ 0) (hv : partialV c α ≠ 0) :
    (inwardContactFrame c α).rotation.act (WithLp.toLp 2 ![1, 0, 0]) = frameX c α := by
  have hflip : inwardFlip.act (WithLp.toLp 2 ![1, 0, 0]) = WithLp.toLp 2 ![1, 0, 0] := by
    apply WithLp.ofLp_injective
    ext i
    rw [Rotation.act_apply]
    fin_cases i <;> simp [inwardFlip, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  simp only [inwardContactFrame, RigidTransform.mul_rotation, Rotation.act_mul,
    contactFrame_rotation, hflip]
  rw [gaussFrame_act_axisX h hu hv]

/-- **With an outward Gauss normal, the `z`-axis of `inwardContactFrame` points into the body (MLS
p. 214):** for a body `{x | h x ≤ 0}` whose Gauss normal at `c(α)` is outward (`IsOutwardNormal`),
the directional derivative of `h` along that `z`-axis is negative. -/
theorem fderiv_inwardContactFrame_axisZ_neg {h : Vec3 → ℝ} {c : (Fin 2 → ℝ) → Vec3}
    {α : Fin 2 → ℝ} (hc : IsOrthogonalAt c α) (hu : partialU c α ≠ 0) (hv : partialV c α ≠ 0)
    (hout : IsOutwardNormal h c α) :
    fderiv ℝ h (c α) ((inwardContactFrame c α).rotation.act (WithLp.toLp 2 ![0, 0, 1])) < 0 := by
  rw [inwardContactFrame_axisZ hc hu hv, map_neg, neg_lt_zero]
  exact hout

/-- **The finger's contact frame is the inward-normal contact frame turned by `ψ` (MLS p. 250 and
eq. (5.34), p. 251, with the entry `−1`):**
`g_{o c_o} · (0, diag(R_ψ, −1)) = inwardContactFrame c_o α_o · (0, R_z(ψ))`, with `R_z(ψ)` the
rotation by `ψ` about the `z`-axis (MLS Example 2.4, p. 53), here the inward normal of the object.
-/
theorem contactFrame_mul_contactOffset (co : (Fin 2 → ℝ) → Vec3) (αo : Fin 2 → ℝ) (ψ : ℝ) :
    contactFrame co αo * contactOffset ψ =
      inwardContactFrame co αo * ⟨Rotation.zRotation ψ, 0⟩ := by
  have hr : contactRotation ψ = inwardFlip * Rotation.zRotation ψ := by
    apply Subtype.ext
    change contactRotationMatrix ψ = inwardFlip.val * (Rotation.zRotation ψ).val
    rw [Rotation.zRotation_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [contactRotationMatrix, inwardFlip, Matrix.mul_apply, Fin.sum_univ_succ]
  ext1
  · simp [inwardContactFrame, contactOffset, hr, mul_assoc]
  · simp [inwardContactFrame, contactOffset]

end Rolling
end RoboLean
