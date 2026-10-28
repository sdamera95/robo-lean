import RoboLean.Grasp.ContactBijection
import RoboLean.Grasp.Manipulability

/-!
# Grasp kinematics with rolling contacts (MLS eqs. (5.40)–(5.42))

MLS Chapter 5, §6.3 "Grasp kinematics with rolling", printed pp. 253–255 (Figure 5.24), with the
summary item 7, p. 257.

**What MLS states.** "Abstractly, the derivation of the grasp kinematics is identical to the fixed
contact case except that the grasp map and hand Jacobian depend on the instantaneous contact
location, which in turn depends on `ηᵢ`, the contact coordinates for each finger. Thus, the contact
kinematics have the form `J_h(θ, x_o, η) θ̇ = Gᵀ(η) V^b_{po}`, `η̇ᵢ = Aᵢ(ηᵢ) V^b_{ofᵢ}` (5.40),
where `η = (η₁, …, η_k) ∈ ℝ^{5k}` is the vector of contact coordinates and `Aᵢ(ηᵢ) ∈ ℝ^{5×6}`
encodes the contact kinematics for each finger, as given in equation (5.28). One additional fact is
needed to extend the previous analysis to the moving contact case: `B_{cᵢ}ᵀ V^b_{ocᵢ} = 0`. This
condition is a statement that the contact point is not allowed to move in any of the constrained
directions. A complete derivation is left as an exercise" (p. 254). "Since `ηᵢ` is a smooth function
of `g_of = g_{po}⁻¹ g_{pfᵢ}` and `g_{pfᵢ}` is a smooth function of `θ`, we can write this constraint
as `J_h(θ, x_o) θ̇ = Gᵀ(θ, x_o) V^b_{po}` (5.41) ... Equation (5.41) is a direct extension of
equation (5.15) to the moving contact case. All of the definitions and properties which held for
fixed contact grasps also hold for moving contact grasps" (p. 255); the only quantity that varies
with `η` is `Ad⁻¹_{g_{ocᵢ}}`, and "we assume that the contact frame is aligned with the normalized
Gauss frame for the object", `g_{ocᵢ} = [[∂c_{oᵢ}/∂α_{oᵢ} M_{oᵢ}⁻¹, n_{oᵢ}, c_{oᵢ}(αᵢ)], [0, 1]]`
(5.42), with `n_{oᵢ}` "the outward pointing surface normal" (p. 255).

**Formalized.**

* `Rolling.contactKinematics cf co η` is `A(η)`: the linear map from `V^b_of` to `(α̇_f, α̇_o, ψ̇)`
  given by the first three lines of (5.28) with `V_{l_o l_f} = Ad⁻¹_{g_{f c_f}(α_f)} V^b_of`, and
  `contactKinematicsMatrix` is its `5 × 6` matrix, rows in the order `(u_f, v_f, u_o, v_o, ψ)` of
  (5.39) and columns the six twist coordinates. (5.28) is `η̇ = A(η) V^b_of` together with `v_z = 0`
  (`kinematicEquations_iff`), and along every motion to which Theorem 5.11 applies
  `η̇ = A(η) V^b_of`: the second line of (5.40) (`hasDerivAt_eq_contactKinematics`).
* `RollingHand` holds contact models, fingers and finger bases as `HandGrasp` does, and a finger
  chart and an object chart for every contact. At contact coordinates `ηᵢ` the contact frame of
  contact `i` is the contact frame of MLS §2 at the object's contact point,
  `Rolling.inwardContactFrame c_{oᵢ} α_{oᵢ}` (origin `c_{oᵢ}(α_{oᵢ})`, `z` along `−n_{oᵢ}`, the
  inward normal when the chart's normal is outward), so that the contact models and friction cones
  of §2 apply unchanged. The book's (5.42) takes the Gauss frame itself (`z` outward) with the same
  models; the two frames differ by the fixed rotation `diag(1, −1, −1)`.
* At fixed `η` a rolling hand is a fixed-contact hand (`toHandGrasp`): `J_h(θ, x_o, η)`, `Gᵀ(η)`,
  `G(η)` and the first line of (5.40) are those of `HandGrasp` with the frames `g_{ocᵢ}(ηᵢ)`, so
  every result of §5 holds at each `η` (for example `isManipulable_iff_surjective`). Conversely a
  fixed-contact hand is a rolling hand at `α_o = 0` with tangent-plane object charts
  (`toHandGrasp_ofHandGrasp`).
* The first line of (5.40) is derived, not assumed: along joint and object trajectories it holds at
  time `t` exactly when every contact satisfies the contact constraint (5.9) of MLS §5 for the
  contact frame frozen at `η(t)` (`graspingConstraint_iff_forall_contactConstraint`). When the
  finger's relative pose at `t` is the contact pose `g_of(ηᵢ(t))`, the frozen relative velocity is
  `−Ad_{(0, R_z(ψ))} V_{l_o l_f}` (`bodyVelocity_fingertipContact_eq`), so the constraint is
  `v_z = 0` for a frictionless contact (which Theorem 5.11 always gives), no sliding
  (`v_x = v_y = v_z = 0`) for a point contact with friction, and pure rolling (p. 249) with
  `v_z = 0` for a soft finger (`softFinger_graspingConstraint_iff`).
* The book's route through `B_{cᵢ}ᵀ V^b_{ocᵢ} = 0`: if the contact frame moves with `η(t)`, the body
  velocity of `g_{fᵢcᵢ}` is the frozen one plus the velocity of the contact frame on the object
  (`bodyVelocity_movingContact`), and the additional fact makes (5.9) for the moving frame
  equivalent to the frozen one. For a point contact with friction or a soft finger the additional
  fact holds exactly when `α̇_o = 0` (`pointContact_constraint_inwardFrameVelocity_eq_zero_iff`,
  `softFinger_constraint_inwardFrameVelocity_eq_zero_iff`): read literally it excludes rolling, and
  the frozen frame is the reading under which (5.40) holds for rolling contacts.
* (5.41): reading the contact coordinates from the relative poses `g_{ofᵢ}` by the local inverses of
  Proposition 5.12, the first line of (5.40) becomes a constraint in `(θ, x_o)` alone
  (`exists_graspingConstraint_iff_graspingConstraintOfPose`). That `θ ↦ ηᵢ(g_{ofᵢ}(θ))` is smooth
  also needs the smoothness of forward kinematics, which is not stated here.

Twist order `(v, ω)`, wrench order `(f, τ)`. Nothing here concerns forces, friction or the
persistence of contact under dynamics.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean

namespace Rolling

open Surface

/-! ### The contact kinematics `A(η)` of (5.40) -/

/-- Supporting lemma for the linearity of MLS eq. (5.28), p. 250: a planar vector literal is
additive in its entries. -/
private lemma vec2_add (a b c d : ℝ) : (![a + c, b + d] : Fin 2 → ℝ) = ![a, b] + ![c, d] := by
  ext i
  fin_cases i <;> simp

/-- Supporting lemma for the linearity of MLS eq. (5.28), p. 250: a planar vector literal is
homogeneous in its entries. -/
private lemma vec2_smul (r a b : ℝ) : (![r * a, r * b] : Fin 2 → ℝ) = r • ![a, b] := by
  ext i
  fin_cases i <;> simp

/-- **The right side of MLS eq. (5.28), p. 250, as a linear map of the relative twist
`V = V^b_{l_o l_f}`:** `V ↦ (α̇_f, α̇_o, ψ̇)` with
`α̇_f = M_f⁻¹ (K_f + K̃_o)⁻¹ ((−ω_y, ω_x) − K̃_o (v_x, v_y))`,
`α̇_o = M_o⁻¹ R_ψ (K_f + K̃_o)⁻¹ ((−ω_y, ω_x) + K_f (v_x, v_y))` and
`ψ̇ = ω_z + T_f M_f α̇_f + T_o M_o α̇_o` (`Matrix.inv` is the matrix inverse). -/
def kinematicRates (Mf Kf Mo Ko : Matrix (Fin 2) (Fin 2) ℝ) (Tf To : Fin 2 → ℝ) (ψ : ℝ) :
    Twist →ₗ[ℝ] ContactCoords where
  toFun V :=
    let af := Mf⁻¹ *ᵥ ((relativeCurvature Kf Ko ψ)⁻¹ *ᵥ
      (![-V.angular 1, V.angular 0] - rotatedCurvature Ko ψ *ᵥ ![V.linear 0, V.linear 1]))
    let ao := Mo⁻¹ *ᵥ (angleMatrix ψ *ᵥ ((relativeCurvature Kf Ko ψ)⁻¹ *ᵥ
      (![-V.angular 1, V.angular 0] + Kf *ᵥ ![V.linear 0, V.linear 1])))
    (af, ao, V.angular 2 + Tf ⬝ᵥ (Mf *ᵥ af) + To ⬝ᵥ (Mo *ᵥ ao))
  map_add' V W := by
    simp only [Twist.add_linear, Twist.add_angular, PiLp.add_apply, neg_add, vec2_add,
      mulVec_add, mulVec_sub, add_sub_add_comm, dotProduct_add, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | abel1
  map_smul' r V := by
    simp only [Twist.smul_linear, Twist.smul_angular, PiLp.smul_apply, smul_eq_mul, ← mul_neg,
      vec2_smul, mulVec_smul, ← smul_sub, ← smul_add, dotProduct_smul, RingHom.id_apply,
      Prod.smul_mk, Prod.mk.injEq]
    refine ⟨trivial, trivial, ?_⟩
    ring

/-- **MLS eq. (5.28), p. 250, as `η̇ = A V` and `v_z = 0`:** the kinematic equations of contact hold
exactly when the rates are the image of the relative twist under `kinematicRates` and the normal
velocity `v_z` vanishes. -/
theorem kinematicEquations_iff {Mf Kf Mo Ko : Matrix (Fin 2) (Fin 2) ℝ} {Tf To : Fin 2 → ℝ}
    {ψ : ℝ} {αf' αo' : Fin 2 → ℝ} {ψ' : ℝ} {V : Twist} :
    KinematicEquations Mf Kf Mo Ko Tf To ψ αf' αo' ψ' V ↔
      (αf', αo', ψ') = kinematicRates Mf Kf Mo Ko Tf To ψ V ∧ V.linear 2 = 0 := by
  simp only [kinematicRates, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, h2, ?_⟩, h4⟩
    rw [← h1, ← h2]
    exact h3
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨h1, h2, ?_, h4⟩
    rw [h1, h2]
    exact h3

/-- **The contact kinematics `A(η)` of MLS eq. (5.40), p. 254 ("`Aᵢ(ηᵢ) ∈ ℝ^{5×6}` encodes the
contact kinematics for each finger, as given in equation (5.28)"):** the linear map from the body
velocity `V^b_of` of the finger relative to the object to the rates `(α̇_f, α̇_o, ψ̇)`, the right
side of (5.28) applied to `V_{l_o l_f} = Ad⁻¹_{g_{f c_f}(α_f)} V^b_of` (eq. (5.27) with the finger's
contact point), with the geometric parameters of the two charts at `η = (α_f, α_o, ψ)`. -/
def contactKinematics (cf co : (Fin 2 → ℝ) → Vec3) (η : ContactCoords) :
    Twist →ₗ[ℝ] ContactCoords :=
  kinematicRates (metricTensor cf η.1) (curvatureTensor cf η.1) (metricTensor co η.2.1)
      (curvatureTensor co η.2.1) (torsionForm cf η.1) (torsionForm co η.2.1) η.2.2 ∘ₗ
    Twist.adjointLinearMap (contactFrame cf η.1)⁻¹

/-- `A(η) V^b_of` is the right side of (5.28) at `V_{l_o l_f} = Ad⁻¹_{g_{f c_f}(α_f)} V^b_of` (MLS
eqs. (5.27)–(5.28), p. 250). -/
theorem contactKinematics_apply (cf co : (Fin 2 → ℝ) → Vec3) (η : ContactCoords) (V : Twist) :
    contactKinematics cf co η V =
      kinematicRates (metricTensor cf η.1) (curvatureTensor cf η.1) (metricTensor co η.2.1)
        (curvatureTensor co η.2.1) (torsionForm cf η.1) (torsionForm co η.2.1) η.2.2
        (Twist.adjoint (contactFrame cf η.1)⁻¹ V) := rfl

/-- **The contact coordinates as a vector of `ℝ⁵` (MLS p. 254, `η ∈ ℝ⁵`)**, in the order
`(u_f, v_f, u_o, v_o, ψ)` of MLS eq. (5.39), p. 253. -/
def stackContactCoords : ContactCoords →ₗ[ℝ] (Fin 5 → ℝ) where
  toFun η := ![η.1 0, η.1 1, η.2.1 0, η.2.1 1, η.2.2]
  map_add' η ζ := by
    ext i
    fin_cases i <;> simp
  map_smul' r η := by
    ext i
    fin_cases i <;> simp

/-- **The `5 × 6` matrix `A(η) ∈ ℝ^{5×6}` of MLS eq. (5.40), p. 254:** rows in the order
`(u_f, v_f, u_o, v_o, ψ)` of (5.39), columns the six twist coordinates `(v, ω)` of
`Twist.coordinates`. -/
def contactKinematicsMatrix (cf co : (Fin 2 → ℝ) → Vec3) (η : ContactCoords) :
    Matrix (Fin 5) (Fin 3 ⊕ Fin 3) ℝ :=
  LinearMap.toMatrix' (stackContactCoords ∘ₗ contactKinematics cf co η ∘ₗ
    Twist.coordinatesEquiv.symm.toLinearMap)

/-- **The matrix `A(η)` acts as the contact kinematics (MLS eq. (5.40), p. 254):** `A(η) V^b_of` in
coordinates. -/
theorem contactKinematicsMatrix_mulVec (cf co : (Fin 2 → ℝ) → Vec3) (η : ContactCoords)
    (V : Twist) :
    contactKinematicsMatrix cf co η *ᵥ V.coordinates =
      stackContactCoords (contactKinematics cf co η V) := by
  rw [contactKinematicsMatrix, LinearMap.toMatrix'_mulVec, ← Twist.coordinatesEquiv_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

variable {cf co : (Fin 2 → ℝ) → Vec3} {Uf Uo : Set (Fin 2 → ℝ)} {αf αo : ℝ → Fin 2 → ℝ}
  {ψ : ℝ → ℝ} {αf' αo' : Fin 2 → ℝ} {ψ' t : ℝ}

/-- **The second line of MLS eq. (5.40), p. 254, `η̇ = A(η) V^b_of`, along a motion:** under the
hypotheses of Theorem 5.11 (`kinematicEquations_of_hasDerivAt`: orthogonal charts, contact
coordinates with actual derivatives at `t` inside the chart domains, a pose curve `g` agreeing near
`t` with `g_of(η(s))`, and the relative curvature form invertible at `η(t)`), for every derivative
`D` of `g` the rates are `(α̇_f, α̇_o, ψ̇) = A(η(t)) V^b_of`. -/
theorem hasDerivAt_eq_contactKinematics (hf : IsOrthogonalChartOn cf Uf)
    (ho : IsOrthogonalChartOn co Uo) (hαf : HasDerivAt αf αf' t) (hαo : HasDerivAt αo αo' t)
    (hψ : HasDerivAt ψ ψ' t) (hft : αf t ∈ Uf) (hot : αo t ∈ Uo)
    (hX : IsUnit (relativeCurvature (curvatureTensor cf (αf t)) (curvatureTensor co (αo t))
      (ψ t)).det) {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t, g s = relativePose cf co (αf s) (αo s) (ψ s)) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    (αf', αo', ψ') =
      contactKinematics cf co (αf t, αo t, ψ t) (RigidTransform.bodyVelocity g D t hD) := by
  exact (kinematicEquations_iff.mp
    (kinematicEquations_of_hasDerivAt hf ho hαf hαo hψ hft hot hX hg hD)).1

/-- **The second line of MLS eq. (5.40), p. 254, in matrices:** under the hypotheses of
`hasDerivAt_eq_contactKinematics`, `(u̇_f, v̇_f, u̇_o, v̇_o, ψ̇) = A(η(t)) V^b_of` with the `5 × 6`
matrix `A(η(t))` and the six coordinates of `V^b_of`. -/
theorem stack_eq_contactKinematicsMatrix_mulVec (hf : IsOrthogonalChartOn cf Uf)
    (ho : IsOrthogonalChartOn co Uo) (hαf : HasDerivAt αf αf' t) (hαo : HasDerivAt αo αo' t)
    (hψ : HasDerivAt ψ ψ' t) (hft : αf t ∈ Uf) (hot : αo t ∈ Uo)
    (hX : IsUnit (relativeCurvature (curvatureTensor cf (αf t)) (curvatureTensor co (αo t))
      (ψ t)).det) {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t, g s = relativePose cf co (αf s) (αo s) (ψ s)) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    ![αf' 0, αf' 1, αo' 0, αo' 1, ψ'] =
      contactKinematicsMatrix cf co (αf t, αo t, ψ t) *ᵥ
        (RigidTransform.bodyVelocity g D t hD).coordinates := by
  rw [contactKinematicsMatrix_mulVec, ← hasDerivAt_eq_contactKinematics hf ho hαf hαo hψ hft hot
    hX hg hD]
  rfl

/-! ### The contact constraint for a frame frozen at the contact -/

/-- Supporting lemma for MLS p. 249: `−Ad_{(0, R_z(ψ))} W` in coordinates, with
`R_z(ψ) = [[cos ψ, −sin ψ, 0], [sin ψ, cos ψ, 0], [0, 0, 1]]` (MLS Example 2.4, p. 53). -/
private lemma neg_adjoint_zRotation (ψ : ℝ) (W : Twist) :
    -Twist.adjoint ⟨Rotation.zRotation ψ, 0⟩ W =
      ⟨WithLp.toLp 2 ![-(Real.cos ψ * W.linear 0 - Real.sin ψ * W.linear 1),
          -(Real.sin ψ * W.linear 0 + Real.cos ψ * W.linear 1), -W.linear 2],
        WithLp.toLp 2 ![-(Real.cos ψ * W.angular 0 - Real.sin ψ * W.angular 1),
          -(Real.sin ψ * W.angular 0 + Real.cos ψ * W.angular 1), -W.angular 2]⟩ := by
  apply Twist.ext <;> apply WithLp.ofLp_injective <;> ext i <;>
    simp only [Twist.neg_linear, Twist.neg_angular, Twist.adjoint_linear, Twist.adjoint_angular,
      Vec3.zero_cross, add_zero, WithLp.ofLp_neg, Pi.neg_apply] <;>
    rw [Rotation.act_apply, Rotation.zRotation_val] <;>
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Supporting lemma for MLS eq. (5.9), p. 235: `B_cᵀ V` for a point contact with friction is the
linear velocity `(v_x, v_y, v_z)` (Table 5.2, p. 219). -/
private lemma pointContact_constraint_eq (μ : ℝ) (hμ : 0 < μ) (V : Twist) :
    (ContactModel.pointContact μ hμ).constraint V = ![V.linear 0, V.linear 1, V.linear 2] := by
  funext j
  fin_cases j <;>
    simp [ContactModel.constraint_apply, ContactModel.pointContact, Wrench.pair, Rotation.xAxis,
      Rotation.yAxis, Rotation.zAxis, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      Fin.sum_univ_succ]

/-- Supporting lemma for MLS eq. (5.9), p. 235: `B_cᵀ V` for a soft finger is `(v_x, v_y, v_z, ω_z)`
(Table 5.2, p. 219). -/
private lemma softFinger_constraint_eq (μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) (V : Twist) :
    (ContactModel.softFinger μ γ hμ hγ).constraint V =
      ![V.linear 0, V.linear 1, V.linear 2, V.angular 2] := by
  funext j
  fin_cases j <;>
    simp [ContactModel.constraint_apply, ContactModel.softFinger, Wrench.pair, Rotation.xAxis,
      Rotation.yAxis, Rotation.zAxis, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      Fin.sum_univ_succ]

/-- Supporting lemma for MLS p. 254 (p. 246, footnote 2): `Ad⁻¹_{(0, diag(1, −1, −1))} V` in
coordinates. -/
private lemma adjoint_inwardFlip_inv (V : Twist) :
    Twist.adjoint (⟨inwardFlip, 0⟩ : RigidTransform)⁻¹ V =
      ⟨WithLp.toLp 2 ![V.linear 0, -V.linear 1, -V.linear 2],
        WithLp.toLp 2 ![V.angular 0, -V.angular 1, -V.angular 2]⟩ := by
  rw [Twist.adjoint_inv]
  apply Twist.ext <;> apply WithLp.ofLp_injective <;> ext i <;>
    simp only [Vec3.zero_cross, sub_zero] <;>
    rw [Rotation.act_apply, Rotation.inv_val] <;>
    fin_cases i <;> simp [inwardFlip, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Supporting lemma for MLS p. 254 with Lemma 5.10, p. 247: the metric tensor of a chart with
`c_u, c_v ≠ 0` kills only `α̇ = 0`, `(M α̇)₀ = (M α̇)₁ = 0 ↔ α̇ = 0`. -/
private lemma metricTensor_mulVec_eq_zero_iff {c : (Fin 2 → ℝ) → Vec3} {α : Fin 2 → ℝ}
    (hu : partialU c α ≠ 0) (hv : partialV c α ≠ 0) (α' : Fin 2 → ℝ) :
    ((metricTensor c α *ᵥ α') 0 = 0 ∧ (metricTensor c α *ᵥ α') 1 = 0) ↔ α' = 0 := by
  have hu' : ‖partialU c α‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hv' : ‖partialV c α‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  simp [metricTensor, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hu', hv', funext_iff,
    Fin.forall_fin_two]

/-- Supporting lemma for MLS p. 249: a planar rotation fixes only the origin, `R_ψ (a, b) = 0`
exactly when `a = b = 0`. -/
private lemma rot2_eq_zero_iff (ψ a b : ℝ) :
    (-(Real.cos ψ * a - Real.sin ψ * b) = 0 ∧ -(Real.sin ψ * a + Real.cos ψ * b) = 0) ↔
      (a = 0 ∧ b = 0) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hsc := Real.sin_sq_add_cos_sq ψ
    constructor
    · linear_combination (-Real.cos ψ) * h1 - Real.sin ψ * h2 - a * hsc
    · linear_combination Real.sin ψ * h1 - Real.cos ψ * h2 - b * hsc
  · rintro ⟨rfl, rfl⟩
    simp

/-- **The constraint of a frictionless contact on a relative twist written in the finger's Gauss
frame (MLS eq. (5.9), p. 235, with p. 249):** for `V = −Ad_{(0, R_z(ψ))} W`, `B_cᵀ V = 0` exactly
when the normal velocity `v_z` of `W` vanishes. -/
theorem frictionless_constraint_neg_adjoint_zRotation (ψ : ℝ) (W : Twist) :
    ContactModel.frictionless.constraint (-Twist.adjoint ⟨Rotation.zRotation ψ, 0⟩ W) = 0 ↔
      W.linear 2 = 0 := by
  rw [ContactModel.frictionless_constraint, neg_adjoint_zRotation]
  simp [Twist.coordinates]

/-- **The constraint of a point contact with friction on a relative twist written in the finger's
Gauss frame (MLS eq. (5.9), p. 235, with p. 249):** for `V = −Ad_{(0, R_z(ψ))} W`, `B_cᵀ V = 0`
exactly when `W` has no linear velocity: no sliding (`v_x = v_y = 0`) and `v_z = 0`. -/
theorem pointContact_constraint_neg_adjoint_zRotation (μ : ℝ) (hμ : 0 < μ) (ψ : ℝ) (W : Twist) :
    (ContactModel.pointContact μ hμ).constraint (-Twist.adjoint ⟨Rotation.zRotation ψ, 0⟩ W) = 0 ↔
      W.linear = 0 := by
  rw [pointContact_constraint_eq, neg_adjoint_zRotation]
  have h := rot2_eq_zero_iff ψ (W.linear 0) (W.linear 1)
  simp only [neg_eq_zero] at h
  simp only [Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_true,
    neg_eq_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  constructor
  · rintro ⟨h0, h1, h2⟩
    obtain ⟨e0, e1⟩ := h.mp ⟨h0, h1⟩
    apply WithLp.ofLp_injective
    ext i
    fin_cases i <;> simp [e0, e1, h2]
  · intro hW
    have e : ∀ i, W.linear i = 0 := fun i => by rw [hW]; rfl
    exact ⟨(h.mpr ⟨e 0, e 1⟩).1, (h.mpr ⟨e 0, e 1⟩).2, e 2⟩

/-- **The constraint of a soft-finger contact on a relative twist written in the finger's Gauss
frame (MLS eq. (5.9), p. 235, with p. 249):** for `V = −Ad_{(0, R_z(ψ))} W`, `B_cᵀ V = 0` exactly
when `W` is a pure rolling (`v_x = v_y = 0`, `ω_z = 0`, p. 249) with `v_z = 0`. -/
theorem softFinger_constraint_neg_adjoint_zRotation (μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) (ψ : ℝ)
    (W : Twist) :
    (ContactModel.softFinger μ γ hμ hγ).constraint
        (-Twist.adjoint ⟨Rotation.zRotation ψ, 0⟩ W) = 0 ↔
      IsRolling W ∧ W.linear 2 = 0 := by
  rw [softFinger_constraint_eq, neg_adjoint_zRotation]
  have h := rot2_eq_zero_iff ψ (W.linear 0) (W.linear 1)
  simp only [neg_eq_zero] at h
  simp only [Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_true, neg_eq_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, IsRolling]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    obtain ⟨e0, e1⟩ := h.mp ⟨h0, h1⟩
    exact ⟨⟨e0, e1, h3⟩, h2⟩
  · rintro ⟨⟨e0, e1, e3⟩, e2⟩
    exact ⟨(h.mpr ⟨e0, e1⟩).1, (h.mpr ⟨e0, e1⟩).2, e2, e3⟩

/-- **The constraint of a point contact with friction on the velocity of the contact frame moving on
the object (MLS p. 254, "`B_{cᵢ}ᵀ V^b_{ocᵢ} = 0`", with Lemma 5.10, p. 247):** for a chart with
`c_u, c_v ≠ 0` and the contact frame of MLS §2 at `c(α)` (`inwardContactFrame`, the Gauss frame
turned by `diag(1, −1, −1)`), whose body velocity along a coordinate curve is
`Ad_{(0, diag(1, −1, −1))}⁻¹ V^b_oc` with `V^b_oc` the twist of Lemma 5.10, `B_cᵀ` of it vanishes
exactly when `α̇ = 0`. -/
theorem pointContact_constraint_inwardFrameVelocity_eq_zero_iff (μ : ℝ) (hμ : 0 < μ)
    {c : (Fin 2 → ℝ) → Vec3} {α : Fin 2 → ℝ} (hu : partialU c α ≠ 0) (hv : partialV c α ≠ 0)
    (α' : Fin 2 → ℝ) :
    (ContactModel.pointContact μ hμ).constraint
        (Twist.adjoint (⟨inwardFlip, 0⟩ : RigidTransform)⁻¹ (contactFrameVelocity c α α')) = 0 ↔
      α' = 0 := by
  rw [pointContact_constraint_eq, adjoint_inwardFlip_inv, ← metricTensor_mulVec_eq_zero_iff hu hv]
  simp [contactFrameVelocity]

/-- **The constraint of a soft-finger contact on the velocity of the contact frame moving on the
object (MLS p. 254, "`B_{cᵢ}ᵀ V^b_{ocᵢ} = 0`", with Lemma 5.10, p. 247):** as for the point contact
with friction, it vanishes exactly when `α̇ = 0`, for a chart with `c_u, c_v ≠ 0`. -/
theorem softFinger_constraint_inwardFrameVelocity_eq_zero_iff (μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    {c : (Fin 2 → ℝ) → Vec3} {α : Fin 2 → ℝ} (hu : partialU c α ≠ 0) (hv : partialV c α ≠ 0)
    (α' : Fin 2 → ℝ) :
    (ContactModel.softFinger μ γ hμ hγ).constraint
        (Twist.adjoint (⟨inwardFlip, 0⟩ : RigidTransform)⁻¹ (contactFrameVelocity c α α')) = 0 ↔
      α' = 0 := by
  rw [softFinger_constraint_eq, adjoint_inwardFlip_inv]
  constructor
  · intro h
    rw [← metricTensor_mulVec_eq_zero_iff hu hv]
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [contactFrameVelocity] at h0 h1
    exact ⟨h0, h1⟩
  · rintro rfl
    simp [contactFrameVelocity]

/-! ### Tangent-plane charts -/

/-- **The tangent-plane chart of a contact frame (MLS p. 214 and p. 246, footnote 2):** for a
contact frame `g = (p, R)` of MLS §2 (`z` along the inward normal), the plane through `p` spanned by
the frame's `x`- and `y`-axes, `c(α) = p + R (α₀, −α₁, 0)`, whose Gauss normal is `−R e_z`. -/
def tangentPlaneChart (g : RigidTransform) (α : Fin 2 → ℝ) : Vec3 :=
  g.applyPoint (WithLp.toLp 2 ![α 0, -α 1, 0])

/-- The linear part `α ↦ R (α₀, −α₁, 0)` of a tangent-plane chart (supporting definition for MLS p.
214 and p. 246, footnote 2). -/
private def tangentPlaneLinear (g : RigidTransform) : (Fin 2 → ℝ) →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap (g.rotation.act ∘ₗ
    { toFun := fun α => WithLp.toLp 2 ![α 0, -α 1, 0]
      map_add' := fun a b => by
        apply WithLp.ofLp_injective
        ext i
        fin_cases i <;> simp [add_comm]
      map_smul' := fun r a => by
        apply WithLp.ofLp_injective
        ext i
        fin_cases i <;> simp })

/-- A tangent-plane chart is affine (supporting lemma for MLS p. 244). -/
private lemma tangentPlaneChart_eq (g : RigidTransform) :
    tangentPlaneChart g = fun γ => g.translation + tangentPlaneLinear g γ := by
  funext γ
  simp [tangentPlaneChart, RigidTransform.applyPoint, tangentPlaneLinear, add_comm]

/-- The derivative of a tangent-plane chart is its linear part (supporting lemma for MLS p. 243). -/
private lemma fderiv_tangentPlaneChart (g : RigidTransform) (α : Fin 2 → ℝ) :
    fderiv ℝ (tangentPlaneChart g) α = tangentPlaneLinear g := by
  rw [tangentPlaneChart_eq]
  exact ((tangentPlaneLinear g).hasFDerivAt.const_add _).fderiv

/-- `c_u = R e_x` for a tangent-plane chart (supporting lemma for MLS p. 243). -/
private lemma partialU_tangentPlaneChart (g : RigidTransform) (α : Fin 2 → ℝ) :
    partialU (tangentPlaneChart g) α = g.rotation.act (WithLp.toLp 2 ![1, 0, 0]) := by
  rw [partialU, fderiv_tangentPlaneChart]
  simp [tangentPlaneLinear]

/-- `c_v = −R e_y` for a tangent-plane chart (supporting lemma for MLS p. 243). -/
private lemma partialV_tangentPlaneChart (g : RigidTransform) (α : Fin 2 → ℝ) :
    partialV (tangentPlaneChart g) α = g.rotation.act (WithLp.toLp 2 ![0, -1, 0]) := by
  rw [partialV, fderiv_tangentPlaneChart]
  simp [tangentPlaneLinear]

/-- Supporting lemma for MLS p. 245: the vectors `e_x` and `−e_y` have unit length. -/
private lemma norm_ex_ey : ‖(WithLp.toLp 2 ![1, 0, 0] : Vec3)‖ = 1 ∧
    ‖(WithLp.toLp 2 ![0, -1, 0] : Vec3)‖ = 1 := by
  constructor <;> simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ]

/-- A tangent-plane chart is orthogonal with unit partials (supporting lemma for MLS p. 244). -/
private lemma tangentPlaneChart_facts (g : RigidTransform) (α : Fin 2 → ℝ) :
    IsOrthogonalAt (tangentPlaneChart g) α ∧ ‖partialU (tangentPlaneChart g) α‖ = 1 ∧
      ‖partialV (tangentPlaneChart g) α‖ = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [IsOrthogonalAt, partialU_tangentPlaneChart, partialV_tangentPlaneChart, Rotation.inner_act]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  · rw [partialU_tangentPlaneChart, Rotation.norm_act, norm_ex_ey.1]
  · rw [partialV_tangentPlaneChart, Rotation.norm_act, norm_ex_ey.2]

/-- The normalized Gauss frame of a tangent-plane chart is `R · diag(1, −1, −1)` (supporting lemma
for MLS p. 245, eq. (5.22)). -/
private lemma gaussFrame_tangentPlaneChart (g : RigidTransform) (α : Fin 2 → ℝ) :
    gaussFrame (tangentPlaneChart g) α = g.rotation * inwardFlip := by
  obtain ⟨ho, hu, hv⟩ := tangentPlaneChart_facts g α
  have hu0 : partialU (tangentPlaneChart g) α ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact zero_ne_one hu
  have hv0 : partialV (tangentPlaneChart g) α ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    exact zero_ne_one hv
  have hx : frameX (tangentPlaneChart g) α = g.rotation.act (WithLp.toLp 2 ![1, 0, 0]) := by
    rw [frameX, hu, inv_one, one_smul, partialU_tangentPlaneChart]
  have hy : frameY (tangentPlaneChart g) α = g.rotation.act (WithLp.toLp 2 ![0, -1, 0]) := by
    rw [frameY, hv, inv_one, one_smul, partialV_tangentPlaneChart]
  apply Subtype.ext
  rw [gaussFrame_val ho hu0 hv0, gaussFrameMatrix, gaussNormal_eq_cross ho, hx, hy,
    ← Rotation.act_cross]
  ext i j
  fin_cases j <;>
    simp [Rotation.act_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.mul_apply,
      inwardFlip, Vec3.cross, crossProduct]

/-- **A tangent-plane chart is an orthogonal chart on all of `ℝ²` (MLS p. 244).** -/
theorem isOrthogonalChartOn_tangentPlaneChart (g : RigidTransform) :
    IsOrthogonalChartOn (tangentPlaneChart g) Set.univ := by
  refine IsOrthogonalChartOn.of_ne_zero isOpen_univ ?_ (fun α _ => (tangentPlaneChart_facts g α).1)
    (fun α _ h => ?_) (fun α _ h => ?_)
  · rw [tangentPlaneChart_eq]
    exact (contDiff_const.add (tangentPlaneLinear g).contDiff).contDiffOn
  · have := (tangentPlaneChart_facts g α).2.1
    rw [h, norm_zero] at this
    exact zero_ne_one this
  · have := (tangentPlaneChart_facts g α).2.2
    rw [h, norm_zero] at this
    exact zero_ne_one this

/-- **The contact frame of MLS §2 of a tangent-plane chart (MLS p. 214, p. 246, footnote 2):**
`inwardContactFrame (tangentPlaneChart g) α = g · (R = I, p = (α₀, −α₁, 0))`; at `α = 0` it is `g`.
-/
theorem inwardContactFrame_tangentPlaneChart (g : RigidTransform) (α : Fin 2 → ℝ) :
    inwardContactFrame (tangentPlaneChart g) α = g * ⟨1, WithLp.toLp 2 ![α 0, -α 1, 0]⟩ := by
  have hF : inwardFlip * inwardFlip = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [inwardFlip]
  ext1
  · simp [inwardContactFrame, gaussFrame_tangentPlaneChart, mul_assoc, hF]
  · simp [inwardContactFrame, tangentPlaneChart, RigidTransform.applyPoint]

end Rolling

/-! ### Hands with rolling contacts -/

/-- **A hand grasping an object with rolling contacts (MLS §6.3, printed pp. 253–255, Figure
5.24):** for each contact `i`, a contact model `(B_{cᵢ}, FC_{cᵢ})` of MLS §2, finger `i` as a serial
chain from its base frame `Sᵢ` to the fingertip frame `Fᵢ` (MLS Chapter 3), the finger base pose
`g_{psᵢ}` in the palm, a chart `c_{fᵢ}` of the fingertip surface in `Fᵢ` and a chart `c_{oᵢ}` of the
object surface in `O` (MLS p. 248). The contact frames are not data: they depend on the contact
coordinates (`contactFrame`). The structure imposes no orientation on the charts: contact from
outside is meant when both chart normals are outward (`Surface.IsOutwardNormal`), and only then
does the `z`-axis `−n_{oᵢ}` of the contact frame point into the object. -/
structure RollingHand (ι : Type*) [Fintype ι] (m n : ι → ℕ) where
  /-- The contact model `(B_{cᵢ}, FC_{cᵢ})` of contact `i`, MLS printed p. 218. -/
  model : (i : ι) → ContactModel Wrench (m i)
  /-- Finger `i` as a serial chain from `Sᵢ` to `Fᵢ`, MLS printed p. 234. -/
  finger : (i : ι) → SerialChain (n i)
  /-- The finger base pose `g_{psᵢ}` in palm coordinates, MLS printed p. 236 (constant). -/
  base : ι → RigidTransform
  /-- The chart `c_{fᵢ}` of the fingertip surface in the fingertip frame `Fᵢ`, MLS p. 248. -/
  fingerChart : ι → (Fin 2 → ℝ) → Vec3
  /-- The chart `c_{oᵢ}` of the object surface at contact `i` in the object frame `O`, MLS p. 248.
  -/
  objectChart : ι → (Fin 2 → ℝ) → Vec3

namespace RollingHand

open Rolling Surface

variable {ι : Type*} [Fintype ι] {m n : ι → ℕ}

/-- **The contact frame `g_{ocᵢ}(ηᵢ)` (MLS p. 255, with the frame convention of MLS §2, p. 214):**
the contact frame of MLS §2 at the object's contact point `c_{oᵢ}(α_{oᵢ})`,
`inwardContactFrame c_{oᵢ} α_{oᵢ}`: the normalized Gauss frame of eq. (5.42) turned by
`diag(1, −1, −1)`, so that its `z`-axis is `−n_{oᵢ}`. -/
def contactFrame (h : RollingHand ι m n) (η : ι → ContactCoords) (i : ι) : RigidTransform :=
  inwardContactFrame (h.objectChart i) (η i).2.1

/-- **The fixed-contact hand at contact coordinates `η` (MLS p. 254, "the derivation of the grasp
kinematics is identical to the fixed contact case except that the grasp map and hand Jacobian depend
on the instantaneous contact location"):** the hand of MLS §5 with the contact frames `g_{ocᵢ}(ηᵢ)`.
-/
def toHandGrasp (h : RollingHand ι m n) (η : ι → ContactCoords) : HandGrasp ι m n :=
  ⟨⟨h.model, h.contactFrame η⟩, h.finger, h.base⟩

/-- The contact frames of the fixed-contact hand at `η` are `g_{ocᵢ}(ηᵢ)` (MLS p. 255). -/
@[simp] theorem toHandGrasp_grasp_frame (h : RollingHand ι m n) (η : ι → ContactCoords) (i : ι) :
    (h.toHandGrasp η).grasp.frame i = h.contactFrame η i := rfl

/-- The fixed-contact hand at `η` keeps the contact models (MLS p. 218). -/
@[simp] theorem toHandGrasp_grasp_model (h : RollingHand ι m n) (η : ι → ContactCoords) (i : ι) :
    (h.toHandGrasp η).grasp.model i = h.model i := rfl

/-- **The hand Jacobian `J_h(θ, x_o, η)` of MLS eq. (5.40), p. 254:** the hand Jacobian (5.14) of
the fixed-contact hand at `η`. -/
def handJacobian (h : RollingHand ι m n) (θ : (i : ι) → Fin (n i) → ℝ) (xo : RigidTransform)
    (η : ι → ContactCoords) : ((i : ι) → Fin (n i) → ℝ) →ₗ[ℝ] ((i : ι) → Fin (m i) → ℝ) :=
  (h.toHandGrasp η).handJacobian θ xo

/-- **The grasp map `G(η)` of MLS §6.3, p. 254:** the grasp map (5.6) with the contact frames
`g_{ocᵢ}(ηᵢ)`. -/
def graspMap (h : RollingHand ι m n) (η : ι → ContactCoords) :
    ((i : ι) → Fin (m i) → ℝ) →ₗ[ℝ] Wrench :=
  (h.toHandGrasp η).grasp.graspMap

/-- **`Gᵀ(η)` of MLS eq. (5.40), p. 254:** the transpose (5.13) of the grasp map with the contact
frames `g_{ocᵢ}(ηᵢ)`. -/
def graspTranspose (h : RollingHand ι m n) (η : ι → ContactCoords) :
    Twist →ₗ[ℝ] ((i : ι) → Fin (m i) → ℝ) :=
  (h.toHandGrasp η).grasp.graspTranspose

/-- **The first line of MLS eq. (5.40), p. 254:** `J_h(θ, x_o, η) θ̇ = Gᵀ(η) V^b_{po}`. -/
def GraspingConstraint (h : RollingHand ι m n) (θ : (i : ι) → Fin (n i) → ℝ) (xo : RigidTransform)
    (η : ι → ContactCoords) (θ' : (i : ι) → Fin (n i) → ℝ) (V : Twist) : Prop :=
  h.handJacobian θ xo η θ' = h.graspTranspose η V

/-- **At fixed `η` the first line of (5.40) is the grasping constraint (5.15) of the fixed-contact
hand (MLS p. 255: "(5.41) is a direct extension of equation (5.15)").** -/
theorem graspingConstraint_iff_toHandGrasp (h : RollingHand ι m n)
    (θ : (i : ι) → Fin (n i) → ℝ) (xo : RigidTransform) (η : ι → ContactCoords)
    (θ' : (i : ι) → Fin (n i) → ℝ) (V : Twist) :
    h.GraspingConstraint θ xo η θ' V ↔ (h.toHandGrasp η).GraspingConstraint θ xo θ' V := Iff.rfl

/-- **"All of the definitions and properties which held for fixed contact grasps also hold for
moving contact grasps" (MLS p. 255), for example summary item 6 (p. 257):** at every `(θ, x_o, η)`,
with onto contact constraint maps (every model of Table 5.2), the grasp is manipulable exactly when
`J_h(θ, x_o, η)` is onto. -/
theorem isManipulable_iff_surjective (h : RollingHand ι m n) (θ : (i : ι) → Fin (n i) → ℝ)
    (xo : RigidTransform) (η : ι → ContactCoords)
    (hB : ∀ i, Function.Surjective (h.model i).constraint) :
    ((h.toHandGrasp η).toMultifingeredGrasp θ xo).IsManipulable ↔
      Function.Surjective (h.handJacobian θ xo η) :=
  (h.toHandGrasp η).isManipulable_iff_surjective θ xo hB

/-- **A fixed-contact hand as a rolling hand (MLS §5, printed pp. 234–237, and §6.3, p. 254):** the
hand with the same contact models, fingers and bases, any finger charts, and as object chart of
contact `i` the tangent plane of its contact frame (`tangentPlaneChart`). -/
def ofHandGrasp (hg : HandGrasp ι m n) (cf : ι → (Fin 2 → ℝ) → Vec3) : RollingHand ι m n :=
  ⟨hg.grasp.model, hg.finger, hg.base, cf, fun i => tangentPlaneChart (hg.grasp.frame i)⟩

/-- **A fixed-contact hand is its rolling hand at `α_o = 0` (MLS p. 254: the fixed contact case is
the rolling case at an instant):** at contact coordinates with `α_{oᵢ} = 0` for every contact, the
fixed-contact hand of `ofHandGrasp hg cf` is `hg`, so every statement about `hg` (rows of MLS §5) is
a statement about a rolling hand at a fixed `η`. -/
theorem toHandGrasp_ofHandGrasp (hg : HandGrasp ι m n) (cf : ι → (Fin 2 → ℝ) → Vec3)
    {η : ι → ContactCoords} (hη : ∀ i, (η i).2.1 = 0) : (ofHandGrasp hg cf).toHandGrasp η = hg := by
  have h1 : (⟨1, WithLp.toLp 2 ![(0 : Fin 2 → ℝ) 0, -(0 : Fin 2 → ℝ) 1, 0]⟩ : RigidTransform) =
      1 := by
    ext1
    · rfl
    · apply WithLp.ofLp_injective
      ext j
      fin_cases j <;> simp
  have hfr : ∀ i, (ofHandGrasp hg cf).contactFrame η i = hg.grasp.frame i := by
    intro i
    simp only [RollingHand.contactFrame, ofHandGrasp]
    rw [inwardContactFrame_tangentPlaneChart, hη i, h1, mul_one]
  obtain ⟨⟨model, frame⟩, finger, base⟩ := hg
  simp only [toHandGrasp, ofHandGrasp] at hfr ⊢
  congr
  funext i
  exact hfr i

/-! ### The first line of (5.40) derived along trajectories -/

/-- Supporting lemma (MLS eq. (2.60), p. 55): pointwise equal pose curves with derivatives have the
same body velocity. -/
private theorem bodyVelocity_congr {g g' : ℝ → RigidTransform} {D D' : HomogeneousMatrix} {t : ℝ}
    (hg : g = g') (hd : HasDerivAt (fun s => (g s).toHomogeneous) D t)
    (hd' : HasDerivAt (fun s => (g' s).toHomogeneous) D' t) :
    RigidTransform.bodyVelocity g D t hd = RigidTransform.bodyVelocity g' D' t hd' := by
  subst hg
  have hDD : D = D' := by
    ext i j
    exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i) j).unique
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hd' i) j)
  subst hDD
  rfl

/-- A constant pose has the derivative `0` (supporting lemma for MLS p. 236). -/
private theorem hasDerivAt_toHomogeneous_const (a : RigidTransform) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => a.toHomogeneous) (0 : HomogeneousMatrix) t :=
  hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => by
    simpa using hasDerivAt_const t (a.toHomogeneous i j)

/-- A constant pose has zero body velocity (supporting lemma for MLS p. 236). -/
private theorem bodyVelocity_const (a : RigidTransform) (t : ℝ) :
    RigidTransform.bodyVelocity (fun _ => a) 0 t (hasDerivAt_toHomogeneous_const a t) = 0 := by
  apply Twist.hat_injective
  rw [RigidTransform.hat_bodyVelocity, Matrix.mul_zero, Twist.hat_zero]

/-- `Ad_g (−ξ) = −Ad_g ξ` (supporting lemma for MLS eq. (2.58), p. 55). -/
private theorem adjoint_neg (g : RigidTransform) (ξ : Twist) :
    Twist.adjoint g (-ξ) = -Twist.adjoint g ξ :=
  map_neg (Twist.adjointLinearMap g) ξ

/-- The body velocity of an inverse pose curve, `V^b_{g⁻¹} = −Ad_g V^b_g` (MLS Lemma 2.16, p. 59).
-/
private theorem bodyVelocity_inv {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}
    (hg : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    RigidTransform.bodyVelocity (fun s => (g s)⁻¹) _ t
        (RigidTransform.hasDerivAt_toHomogeneous_inv hg) =
      -Twist.adjoint (g t) (RigidTransform.bodyVelocity g D t hg) := by
  rw [RigidTransform.bodyVelocity_eq_neg_spatialVelocity_inv hg,
    RigidTransform.spatialVelocity_eq_adjoint_body
      (RigidTransform.hasDerivAt_toHomogeneous_inv hg),
    adjoint_neg, neg_neg, Twist.adjoint_adjoint_inv]

/-- The body velocity of `s ↦ P(s)⁻¹ C` with `C` fixed is `−Ad_{C⁻¹ P(t)} V^b_P` (MLS Proposition
2.15 and Lemma 2.16, pp. 58–59). -/
private theorem bodyVelocity_inv_mul_const {P : ℝ → RigidTransform} {E : HomogeneousMatrix}
    {t : ℝ} (hE : HasDerivAt (fun s => (P s).toHomogeneous) E t) (C : RigidTransform)
    {g : ℝ → RigidTransform} (hg : ∀ s, g s = (P s)⁻¹ * C) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    RigidTransform.bodyVelocity g D t hD =
      -Twist.adjoint (C⁻¹ * P t) (RigidTransform.bodyVelocity P E t hE) := by
  have hPi := RigidTransform.hasDerivAt_toHomogeneous_inv hE
  have hC := hasDerivAt_toHomogeneous_const C t
  rw [bodyVelocity_congr (funext hg) hD (RigidTransform.hasDerivAt_toHomogeneous_mul hPi hC),
    RigidTransform.bodyVelocity_mul hPi hC, bodyVelocity_inv hE, bodyVelocity_const, add_zero,
    adjoint_neg, Twist.adjoint_mul]

/-- The derivative of the first component of a curve in a product (supporting lemma for the contact
coordinates `η = (α_f, α_o, ψ)` of MLS p. 249). -/
private theorem hasDerivAt_fst {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → E × F} {f' : E × F} {t : ℝ}
    (h : HasDerivAt f f' t) : HasDerivAt (fun s => (f s).1) f'.1 t :=
  (ContinuousLinearMap.fst ℝ E F).hasFDerivAt.comp_hasDerivAt t h

/-- The derivative of the second component of a curve in a product (supporting lemma for the contact
coordinates `η = (α_f, α_o, ψ)` of MLS p. 249). -/
private theorem hasDerivAt_snd {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → E × F} {f' : E × F} {t : ℝ}
    (h : HasDerivAt f f' t) : HasDerivAt (fun s => (f s).2) f'.2 t :=
  (ContinuousLinearMap.snd ℝ E F).hasFDerivAt.comp_hasDerivAt t h

/-- **The relative pose of finger `i` with respect to the object,
`g_{ofᵢ} = g_{po}⁻¹ g_{psᵢ} g_{sᵢfᵢ}(θᵢ)` (MLS p. 255).** -/
def fingerPose (h : RollingHand ι m n) (i : ι) (θi : Fin (n i) → ℝ) (xo : RigidTransform) :
    RigidTransform :=
  xo⁻¹ * (h.base i * (h.finger i).fk θi)

/-- **The first line of MLS eq. (5.40), p. 254, derived from the contact constraint (5.9) with the
contact frames frozen at `η`:** along joint trajectories `θ(s)` and an object trajectory `g_{po}(s)`
with actual derivatives, `J_h(θ, x_o, η) θ̇ = Gᵀ(η) V^b_{po}` holds at `t` exactly when every
contact satisfies (5.9) for the contact frame `g_{ocᵢ}(ηᵢ)` held fixed on the object (`η` is the
value of the contact coordinates at `t`). -/
theorem graspingConstraint_iff_forall_contactConstraint (h : RollingHand ι m n)
    (η : ι → ContactCoords) {θ : ℝ → (i : ι) → Fin (n i) → ℝ} {θ' : (i : ι) → Fin (n i) → ℝ}
    {xo : ℝ → RigidTransform} {Do : HomogeneousMatrix} {t : ℝ}
    (hθ : ∀ i l, HasDerivAt (fun s => θ s i l) (θ' i l) t)
    (ho : HasDerivAt (fun s => (xo s).toHomogeneous) Do t) :
    h.GraspingConstraint (θ t) (xo t) η θ' (RigidTransform.bodyVelocity xo Do t ho) ↔
      ∀ i, (h.toHandGrasp η).ContactConstraint i (fun s => θ s i) xo t :=
  (h.toHandGrasp η).graspingConstraint_iff_forall_contactConstraint hθ ho

/-- **The frozen contact velocity is the relative velocity of the two surfaces at the contact (MLS
pp. 249–250):** if at time `t` the relative pose of finger `i` is the contact pose `g_of(ηᵢ)` of its
charts, the body velocity of `g_{fᵢcᵢ} = g_{pfᵢ}⁻¹ g_{po} g_{ocᵢ}(ηᵢ)` (contact frame frozen at
`ηᵢ`) is `−Ad_{(0, R_z(ψᵢ))} V_{l_o l_f}`, with `V_{l_o l_f} = Ad⁻¹_{g_{f c_f}(α_{fᵢ})} V^b_{ofᵢ}`
the relative twist of eq. (5.27) and `V^b_{ofᵢ}` the body velocity of `g_{ofᵢ}(s)`. -/
theorem bodyVelocity_fingertipContact_eq (h : RollingHand ι m n) (η : ι → ContactCoords) (i : ι)
    {θ : ℝ → Fin (n i) → ℝ} {xo : ℝ → RigidTransform} {t : ℝ}
    (hc : h.fingerPose i (θ t) (xo t) = relativePoseMap (h.fingerChart i) (h.objectChart i) (η i))
    {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => ((h.toHandGrasp η).fingertipContact i (θ s) (xo s)).toHomogeneous)
      D t)
    {E : HomogeneousMatrix}
    (hE : HasDerivAt (fun s => (h.fingerPose i (θ s) (xo s)).toHomogeneous) E t) :
    RigidTransform.bodyVelocity (fun s => (h.toHandGrasp η).fingertipContact i (θ s) (xo s)) D t
        hD =
      -Twist.adjoint ⟨Rotation.zRotation (η i).2.2, 0⟩
        (Twist.adjoint (Surface.contactFrame (h.fingerChart i) (η i).1)⁻¹
          (RigidTransform.bodyVelocity (fun s => h.fingerPose i (θ s) (xo s)) E t hE)) := by
  have hg : ∀ s, (h.toHandGrasp η).fingertipContact i (θ s) (xo s) =
      (h.fingerPose i (θ s) (xo s))⁻¹ * h.contactFrame η i := by
    intro s
    simp only [HandGrasp.fingertipContact, fingerPose, toHandGrasp]
    group
  rw [bodyVelocity_inv_mul_const hE _ hg hD]
  have hCP : (h.contactFrame η i)⁻¹ * h.fingerPose i (θ t) (xo t) =
      ⟨Rotation.zRotation (η i).2.2, 0⟩ * (Surface.contactFrame (h.fingerChart i) (η i).1)⁻¹ := by
    rw [hc, relativePoseMap, relativePose, contactFrame_mul_contactOffset,
      RollingHand.contactFrame]
    group
  rw [hCP, Twist.adjoint_mul]

/-- **The contact constraint with the frame frozen at the contact, in terms of the relative twist
(MLS eq. (5.9), p. 235, and pp. 249–250):** along trajectories with actual derivatives, if the
relative pose of finger `i` at `t` is the contact pose `g_of(ηᵢ)`, contact `i` satisfies (5.9) for
the frozen frame exactly when `B_{cᵢ}ᵀ (−Ad_{(0, R_z(ψᵢ))} V_{l_o l_f}) = 0`. -/
theorem contactConstraint_iff (h : RollingHand ι m n) (η : ι → ContactCoords) (i : ι)
    {θ : ℝ → Fin (n i) → ℝ} {θ' : Fin (n i) → ℝ} {xo : ℝ → RigidTransform} {Do : HomogeneousMatrix}
    {t : ℝ} (hθ : ∀ l, HasDerivAt (fun s => θ s l) (θ' l) t)
    (ho : HasDerivAt (fun s => (xo s).toHomogeneous) Do t)
    (hc : h.fingerPose i (θ t) (xo t) = relativePoseMap (h.fingerChart i) (h.objectChart i) (η i))
    {E : HomogeneousMatrix}
    (hE : HasDerivAt (fun s => (h.fingerPose i (θ s) (xo s)).toHomogeneous) E t) :
    (h.toHandGrasp η).ContactConstraint i θ xo t ↔
      (h.model i).constraint (-Twist.adjoint ⟨Rotation.zRotation (η i).2.2, 0⟩
        (Twist.adjoint (Surface.contactFrame (h.fingerChart i) (η i).1)⁻¹
          (RigidTransform.bodyVelocity (fun s => h.fingerPose i (θ s) (xo s)) E t hE))) = 0 := by
  constructor
  · rintro ⟨D, hD, hcon⟩
    rw [bodyVelocity_fingertipContact_eq h η i hc hD hE] at hcon
    exact hcon
  · intro H
    obtain ⟨D, hD⟩ := (h.toHandGrasp η).hasDerivAt_fingertipContact i hθ ho
    exact ⟨D, hD, by rw [bodyVelocity_fingertipContact_eq h η i hc hD hE]; exact H⟩

/-- **MLS eq. (5.40), p. 254, for a hand of soft fingers: the first line holds exactly when every
finger rolls.** Let every contact be a soft finger (MLS eq. (5.4), p. 217) and let the hand move
along joint and object trajectories with actual derivatives, the contact coordinates `η(s)` of every
finger having actual derivatives at `t` in the domains of orthogonal charts and the relative pose of
every finger agreeing near `t` with `g_of(ηᵢ(s))` (contact maintained, MLS p. 249). Then
`J_h(θ, x_o, η(t)) θ̇ = Gᵀ(η(t)) V^b_{po}` holds at `t` exactly when every relative twist
`V_{l_o l_f}` is a pure rolling (p. 249); `v_z = 0` holds by Theorem 5.11. -/
theorem softFinger_graspingConstraint_iff (μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    (h : RollingHand ι (fun _ => 4) n)
    (hmodel : ∀ i, h.model i = ContactModel.softFinger μ γ hμ hγ)
    {Uf Uo : ι → Set (Fin 2 → ℝ)} (hf : ∀ i, IsOrthogonalChartOn (h.fingerChart i) (Uf i))
    (ho : ∀ i, IsOrthogonalChartOn (h.objectChart i) (Uo i))
    {θ : ℝ → (i : ι) → Fin (n i) → ℝ} {θ' : (i : ι) → Fin (n i) → ℝ} {xo : ℝ → RigidTransform}
    {Do : HomogeneousMatrix} {η : ℝ → ι → ContactCoords} {η' : ι → ContactCoords} {t : ℝ}
    (hθ : ∀ i l, HasDerivAt (fun s => θ s i l) (θ' i l) t)
    (ho' : HasDerivAt (fun s => (xo s).toHomogeneous) Do t)
    (hη : ∀ i, HasDerivAt (fun s => η s i) (η' i) t) (hηf : ∀ i, (η t i).1 ∈ Uf i)
    (hηo : ∀ i, (η t i).2.1 ∈ Uo i)
    (hg : ∀ i, ∀ᶠ s in 𝓝 t, h.fingerPose i (θ s i) (xo s) =
      relativePoseMap (h.fingerChart i) (h.objectChart i) (η s i))
    {E : ι → HomogeneousMatrix}
    (hE : ∀ i, HasDerivAt (fun s => (h.fingerPose i (θ s i) (xo s)).toHomogeneous) (E i) t) :
    h.GraspingConstraint (θ t) (xo t) (η t) θ' (RigidTransform.bodyVelocity xo Do t ho') ↔
      ∀ i, IsRolling (Twist.adjoint (Surface.contactFrame (h.fingerChart i) (η t i).1)⁻¹
        (RigidTransform.bodyVelocity (fun s => h.fingerPose i (θ s i) (xo s)) (E i) t (hE i))) := by
  rw [graspingConstraint_iff_forall_contactConstraint h (η t) hθ ho']
  refine forall_congr' fun i => ?_
  rw [contactConstraint_iff h (η t) i (hθ i) ho' (hg i).self_of_nhds (hE i), hmodel i,
    softFinger_constraint_neg_adjoint_zRotation]
  have hηi := hη i
  have hce := contactEquations_of_hasDerivAt (hf i) (ho i) (hasDerivAt_fst hηi)
    (hasDerivAt_fst (hasDerivAt_snd hηi)) (hasDerivAt_snd (hasDerivAt_snd hηi)) (hηf i) (hηo i)
    (hg i) (hE i)
  exact and_iff_left hce.linear_normal

/-! ### The book's route: the contact frame moving with the contact -/

/-- **The contact frame moving with the contact (MLS p. 254):** with the contact frame
`g_{ocᵢ}(ηᵢ(s))` following the contact coordinates, the body velocity of
`g_{fᵢcᵢ}(s) = g_{pfᵢ}(s)⁻¹ g_{po}(s) g_{ocᵢ}(ηᵢ(s))` is that of the frame frozen at `ηᵢ(t)` plus
the body velocity of the contact frame on the object, `Ad_{(0, diag(1, −1, −1))}⁻¹ V^b_{oc}` with
`V^b_oc` the twist of Lemma 5.10 (p. 247) for the object chart. -/
theorem bodyVelocity_movingContact (h : RollingHand ι m n) (i : ι) {θ : ℝ → Fin (n i) → ℝ}
    {xo : ℝ → RigidTransform} {η : ℝ → ι → ContactCoords} {αo' : Fin 2 → ℝ} {t : ℝ}
    {Uo : Set (Fin 2 → ℝ)} (ho : IsOrthogonalChartOn (h.objectChart i) Uo)
    (hη : HasDerivAt (fun s => (η s i).2.1) αo' t) (hot : (η t i).2.1 ∈ Uo)
    {P : HomogeneousMatrix}
    (hP : HasDerivAt (fun s => (h.fingerPose i (θ s) (xo s)).toHomogeneous) P t)
    {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => ((h.toHandGrasp (η s)).fingertipContact i (θ s)
      (xo s)).toHomogeneous) D t)
    {E : HomogeneousMatrix}
    (hE : HasDerivAt (fun s => ((h.toHandGrasp (η t)).fingertipContact i (θ s)
      (xo s)).toHomogeneous) E t) :
    RigidTransform.bodyVelocity (fun s => (h.toHandGrasp (η s)).fingertipContact i (θ s) (xo s))
        D t hD =
      RigidTransform.bodyVelocity (fun s => (h.toHandGrasp (η t)).fingertipContact i (θ s) (xo s))
          E t hE +
        Twist.adjoint (⟨inwardFlip, 0⟩ : RigidTransform)⁻¹
          (contactFrameVelocity (h.objectChart i) (η t i).2.1 αo') := by
  obtain ⟨DA, hA⟩ := exists_hasDerivAt_contactFrame ho hη hot
  have hF := hasDerivAt_toHomogeneous_const (⟨inwardFlip, 0⟩ : RigidTransform) t
  have hQ := RigidTransform.hasDerivAt_toHomogeneous_mul hA hF
  have hPi := RigidTransform.hasDerivAt_toHomogeneous_inv hP
  have hM := RigidTransform.hasDerivAt_toHomogeneous_mul hPi hQ
  have hgM : (fun s => (h.toHandGrasp (η s)).fingertipContact i (θ s) (xo s)) =
      fun s => (h.fingerPose i (θ s) (xo s))⁻¹ *
        (Surface.contactFrame (h.objectChart i) (η s i).2.1 * ⟨inwardFlip, 0⟩) := by
    funext s
    simp only [HandGrasp.fingertipContact, fingerPose, toHandGrasp, RollingHand.contactFrame,
      inwardContactFrame]
    group
  have hC := hasDerivAt_toHomogeneous_const (h.contactFrame (η t) i) t
  have hN := RigidTransform.hasDerivAt_toHomogeneous_mul hPi hC
  have hgF : (fun s => (h.toHandGrasp (η t)).fingertipContact i (θ s) (xo s)) =
      fun s => (h.fingerPose i (θ s) (xo s))⁻¹ * h.contactFrame (η t) i := by
    funext s
    simp only [HandGrasp.fingertipContact, fingerPose, toHandGrasp]
    group
  rw [bodyVelocity_congr hgM hD hM, RigidTransform.bodyVelocity_mul hPi hQ,
    RigidTransform.bodyVelocity_mul hA hF, bodyVelocity_const, add_zero,
    Surface.bodyVelocity_contactFrame ho hη hot hA, bodyVelocity_congr hgF hE hN,
    RigidTransform.bodyVelocity_mul hPi hC, bodyVelocity_const, add_zero]
  rfl

/-- **The additional fact of MLS p. 254 reduces (5.9) for the moving frame to (5.9) for the frozen
frame:** under the hypotheses of `bodyVelocity_movingContact`, if `B_{cᵢ}ᵀ V^b_{ocᵢ} = 0` ("the
contact point is not allowed to move in any of the constrained directions"), then `B_{cᵢ}ᵀ` vanishes
on the moving-frame velocity exactly when it vanishes on the frozen-frame velocity. With
`pointContact_constraint_inwardFrameVelocity_eq_zero_iff` and
`softFinger_constraint_inwardFrameVelocity_eq_zero_iff`, the fact holds for those models only when
`α̇_{oᵢ} = 0`. -/
theorem constraint_movingContact_iff (h : RollingHand ι m n) (i : ι) {θ : ℝ → Fin (n i) → ℝ}
    {xo : ℝ → RigidTransform} {η : ℝ → ι → ContactCoords} {αo' : Fin 2 → ℝ} {t : ℝ}
    {Uo : Set (Fin 2 → ℝ)} (ho : IsOrthogonalChartOn (h.objectChart i) Uo)
    (hη : HasDerivAt (fun s => (η s i).2.1) αo' t) (hot : (η t i).2.1 ∈ Uo)
    {P : HomogeneousMatrix}
    (hP : HasDerivAt (fun s => (h.fingerPose i (θ s) (xo s)).toHomogeneous) P t)
    {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => ((h.toHandGrasp (η s)).fingertipContact i (θ s)
      (xo s)).toHomogeneous) D t)
    {E : HomogeneousMatrix}
    (hE : HasDerivAt (fun s => ((h.toHandGrasp (η t)).fingertipContact i (θ s)
      (xo s)).toHomogeneous) E t)
    (hfact : (h.model i).constraint (Twist.adjoint (⟨inwardFlip, 0⟩ : RigidTransform)⁻¹
      (contactFrameVelocity (h.objectChart i) (η t i).2.1 αo')) = 0) :
    (h.model i).constraint (RigidTransform.bodyVelocity
        (fun s => (h.toHandGrasp (η s)).fingertipContact i (θ s) (xo s)) D t hD) = 0 ↔
      (h.model i).constraint (RigidTransform.bodyVelocity
        (fun s => (h.toHandGrasp (η t)).fingertipContact i (θ s) (xo s)) E t hE) = 0 := by
  rw [bodyVelocity_movingContact h i ho hη hot hP hD hE, map_add, hfact, add_zero]

/-! ### (5.41): the contact coordinates read from the relative poses -/

/-- **MLS eq. (5.41), p. 255, `J_h(θ, x_o) θ̇ = Gᵀ(θ, x_o) V^b_{po}`:** the first line of (5.40)
with the contact coordinates of finger `i` read from its relative pose
`g_{ofᵢ} = g_{po}⁻¹ g_{pfᵢ}(θ)` by a readout `ηOf i`. -/
def GraspingConstraintOfPose (h : RollingHand ι m n) (ηOf : ι → RigidTransform → ContactCoords)
    (θ : (i : ι) → Fin (n i) → ℝ) (xo : RigidTransform) (θ' : (i : ι) → Fin (n i) → ℝ)
    (V : Twist) : Prop :=
  h.GraspingConstraint θ xo (fun i => ηOf i (h.fingerPose i (θ i) xo)) θ' V

/-- **MLS eq. (5.41), p. 255, from Proposition 5.12 (p. 254):** at contact coordinates `η₀` in the
domains of orthogonal charts with every relative curvature form invertible, there are neighbourhoods
`Nᵢ` of `η₀ᵢ` and readouts `Ψᵢ`, `C¹` at the contact poses `g_of(η₀ᵢ)`, such that whenever the
contact coordinates `η` lie in the `Nᵢ` and every finger is at its contact pose
(`g_{ofᵢ} = g_of(ηᵢ)`), the first line of (5.40) at `η` is (5.41) at `(θ, x_o)` with the contact
coordinates read as `Ψᵢ(g_{ofᵢ})`. -/
theorem exists_graspingConstraint_iff_graspingConstraintOfPose (h : RollingHand ι m n)
    {Uf Uo : ι → Set (Fin 2 → ℝ)} (hf : ∀ i, IsOrthogonalChartOn (h.fingerChart i) (Uf i))
    (ho : ∀ i, IsOrthogonalChartOn (h.objectChart i) (Uo i)) {η₀ : ι → ContactCoords}
    (hηf : ∀ i, (η₀ i).1 ∈ Uf i) (hηo : ∀ i, (η₀ i).2.1 ∈ Uo i)
    (hX : ∀ i, IsUnit (relativeCurvature (curvatureTensor (h.fingerChart i) (η₀ i).1)
      (curvatureTensor (h.objectChart i) (η₀ i).2.1) (η₀ i).2.2).det) :
    ∃ N : ι → Set ContactCoords, ∃ Ψ : ι → PoseCoords → ContactCoords,
      (∀ i, N i ∈ 𝓝 (η₀ i)) ∧
      (∀ i, ContDiffAt ℝ 1 (Ψ i)
        (poseCoords (relativePoseMap (h.fingerChart i) (h.objectChart i) (η₀ i)))) ∧
      ∀ (θ : (i : ι) → Fin (n i) → ℝ) (xo : RigidTransform) (η : ι → ContactCoords),
        (∀ i, η i ∈ N i) →
        (∀ i, h.fingerPose i (θ i) xo =
          relativePoseMap (h.fingerChart i) (h.objectChart i) (η i)) →
        ∀ (θ' : (i : ι) → Fin (n i) → ℝ) (V : Twist),
          h.GraspingConstraint θ xo η θ' V ↔
            h.GraspingConstraintOfPose (fun i g => Ψ i (poseCoords g)) θ xo θ' V := by
  have H := fun i => exists_local_inverse_relativePoseMap_of_isOrthogonalChartOn (hf i) (ho i)
    (hηf i) (hηo i) (hX i)
  choose N hN Ψ hΨ _ _ hinv using H
  refine ⟨N, Ψ, hN, hΨ, ?_⟩
  intro θ xo η hηN hpose θ' V
  have hη : (fun i => Ψ i (poseCoords (h.fingerPose i (θ i) xo))) = η := by
    funext i
    rw [hpose i, hinv i (η i) (hηN i)]
  rw [GraspingConstraintOfPose, hη]

end RollingHand

end RoboLean
