import RoboLean.Grasp.ContactCoordinates

/-!
# The equations of contact: the algebraic core of Montana's theorem

MLS Chapter 5, §6.2, printed pp. 249–252 and 254: Theorem 5.11 (5.28), its proof (5.37), Corollary
5.11.1 (5.38) and the rank condition of Proposition 5.12.

**What MLS states.** With `(v_x, v_y, v_z, ω_x, ω_y, ω_z) = V^b_{l_o l_f}` (p. 249), the kinematic
equations of contact are `α̇_f = M_f⁻¹ (K_f + K̃_o)⁻¹ ([−ω_y; ω_x] − K̃_o [v_x; v_y])`,
`α̇_o = M_o⁻¹ R_ψ (K_f + K̃_o)⁻¹ ([−ω_y; ω_x] + K_f [v_x; v_y])`,
`ψ̇ = ω_z + T_f M_f α̇_f + T_o M_o α̇_o`, `0 = v_z` (5.28, p. 250). The proof equates components
(5.37, p. 252): `[M_f α̇_f; 0] + [v_x; v_y; v_z] = [R_ψ M_o α̇_o; 0]` and
`[K_f M_f α̇_f; T_f M_f α̇_f] + [ω_y; −ω_x; ω_z] = [0; 0; ψ̇] − [R_ψ K_o M_o α̇_o; T_o M_o α̇_o]`,
and "After some algebraic manipulation, we can write equation (5.37) in the form given by equation
(5.28)". "The equations of contact only make sense when the relative curvature is nonsingular ... we
shall assume that all manipulation occurs in an open set on which the relative curvature is
invertible" (p. 251). "For pure rolling contact we have `v_x = v_y = 0` and `ω_z = 0` and for pure
sliding contact we have `ω_x = ω_y = ω_z = 0`" (p. 249); Corollary 5.11.1 (5.38, p. 252) is (5.28)
for rolling. Proposition 5.12 (p. 254) asks that `K_f + R_ψ K_o R_ψᵀ` be "full rank".

**Formalized.** `ContactEquations` is (5.37) and `KinematicEquations` is (5.28), as propositions on
the geometric parameters, the contact angle, the rates `(α̇_f, α̇_o, ψ̇)` and a twist `V` (twist
order `(v, ω)`, components indexed `0, 1, 2` for `x, y, z`). They are equivalent when `M_f`, `M_o`
and the relative curvature form are invertible (`contactEquations_iff_kinematicEquations`), the
book's hypothesis of p. 251 together with the invertibility of the metric tensors (automatic for
orthogonal charts). `IsRolling` and `IsSliding` are the definitions of p. 249; `RollingEquations` is
(5.38) and follows from (5.28) under rolling (`rollingEquations_of_kinematicEquations`). The
derivative-level core of Proposition 5.12: with zero relative velocity, (5.37) forces zero contact
rates for every choice of rates exactly when the relative curvature form is invertible
(`contactEquations_zero_injective_iff`).
-/

noncomputable section

open Matrix

namespace RoboLean
namespace Rolling

variable {Mf Kf Mo Ko : Matrix (Fin 2) (Fin 2) ℝ} {Tf To : Fin 2 → ℝ} {ψ : ℝ}
  {αf' αo' : Fin 2 → ℝ} {ψ' : ℝ} {V : Twist}

/-- **MLS eq. (5.37), p. 252, the components of (5.33):** `M_f α̇_f + (v_x, v_y) = R_ψ M_o α̇_o`,
`v_z = 0`, `K_f M_f α̇_f + (ω_y, −ω_x) = −R_ψ K_o M_o α̇_o` and
`T_f M_f α̇_f + ω_z = ψ̇ − T_o M_o α̇_o`, for the geometric parameters `(M, K, T)` of the finger
(`f`) and object (`o`) charts, the contact angle `ψ`, the rates `(α̇_f, α̇_o, ψ̇)` and the twist
`V = (v, ω)`. -/
structure ContactEquations (Mf Kf Mo Ko : Matrix (Fin 2) (Fin 2) ℝ) (Tf To : Fin 2 → ℝ) (ψ : ℝ)
    (αf' αo' : Fin 2 → ℝ) (ψ' : ℝ) (V : Twist) : Prop where
  /-- Tangential linear rows of (5.37): `M_f α̇_f + (v_x, v_y) = R_ψ M_o α̇_o`. -/
  linear_tangent : Mf *ᵥ αf' + ![V.linear 0, V.linear 1] = angleMatrix ψ *ᵥ (Mo *ᵥ αo')
  /-- Normal linear row of (5.37): `v_z = 0`. -/
  linear_normal : V.linear 2 = 0
  /-- Tangential angular rows of (5.37): `K_f M_f α̇_f + (ω_y, −ω_x) = −R_ψ K_o M_o α̇_o`. -/
  angular_tangent : Kf *ᵥ (Mf *ᵥ αf') + ![V.angular 1, -V.angular 0] =
    -(angleMatrix ψ *ᵥ (Ko *ᵥ (Mo *ᵥ αo')))
  /-- Normal angular row of (5.37): `T_f M_f α̇_f + ω_z = ψ̇ − T_o M_o α̇_o`. -/
  angular_normal : Tf ⬝ᵥ (Mf *ᵥ αf') + V.angular 2 = ψ' - To ⬝ᵥ (Mo *ᵥ αo')

/-- **MLS Theorem 5.11, eq. (5.28), p. 250, the kinematic equations of contact:**
`α̇_f = M_f⁻¹ (K_f + K̃_o)⁻¹ ((−ω_y, ω_x) − K̃_o (v_x, v_y))`,
`α̇_o = M_o⁻¹ R_ψ (K_f + K̃_o)⁻¹ ((−ω_y, ω_x) + K_f (v_x, v_y))`,
`ψ̇ = ω_z + T_f M_f α̇_f + T_o M_o α̇_o` and `v_z = 0`, with `K̃_o = R_ψ K_o R_ψ` (`Matrix.inv` is
the matrix inverse). -/
structure KinematicEquations (Mf Kf Mo Ko : Matrix (Fin 2) (Fin 2) ℝ) (Tf To : Fin 2 → ℝ) (ψ : ℝ)
    (αf' αo' : Fin 2 → ℝ) (ψ' : ℝ) (V : Twist) : Prop where
  /-- First line of (5.28): the finger contact rate. -/
  rate_finger : αf' = Mf⁻¹ *ᵥ ((relativeCurvature Kf Ko ψ)⁻¹ *ᵥ
    (![-V.angular 1, V.angular 0] - rotatedCurvature Ko ψ *ᵥ ![V.linear 0, V.linear 1]))
  /-- Second line of (5.28): the object contact rate. -/
  rate_object : αo' = Mo⁻¹ *ᵥ (angleMatrix ψ *ᵥ ((relativeCurvature Kf Ko ψ)⁻¹ *ᵥ
    (![-V.angular 1, V.angular 0] + Kf *ᵥ ![V.linear 0, V.linear 1])))
  /-- Third line of (5.28): the rate of the contact angle. -/
  rate_angle : ψ' = V.angular 2 + Tf ⬝ᵥ (Mf *ᵥ αf') + To ⬝ᵥ (Mo *ᵥ αo')
  /-- Fourth line of (5.28): `0 = v_z`. -/
  normal : V.linear 2 = 0

/-- Supporting lemma for the algebra of MLS p. 252: for an invertible matrix `A`, `x = A⁻¹ y`
exactly when `A x = y`. -/
private lemma eq_inv_mulVec_iff {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : IsUnit A.det)
    {x y : Fin 2 → ℝ} : x = A⁻¹ *ᵥ y ↔ A *ᵥ x = y := by
  constructor
  · rintro rfl
    rw [mulVec_mulVec, mul_nonsing_inv _ hA, one_mulVec]
  · rintro rfl
    rw [mulVec_mulVec, nonsing_inv_mul _ hA, one_mulVec]

/-- Supporting lemma for MLS p. 250: `R_ψ R_ψ x = x`. -/
private lemma angleMatrix_mulVec_mulVec (ψ : ℝ) (x : Fin 2 → ℝ) :
    angleMatrix ψ *ᵥ (angleMatrix ψ *ᵥ x) = x := by
  rw [mulVec_mulVec, angleMatrix_mul_self, one_mulVec]

/-- Supporting lemma for MLS eq. (5.37), p. 252: `(ω_y, −ω_x) = −(−ω_y, ω_x)`. -/
private lemma vec_neg_swap (a b : ℝ) : ![a, -b] = -![-a, b] := by
  ext i
  fin_cases i <;> simp

/-- Supporting lemma for MLS Proposition 5.12, p. 254 (zero relative velocity): the zero vector of
the plane written with its two coordinates. -/
private lemma vec_zero_zero : (![0, 0] : Fin 2 → ℝ) = 0 := by
  ext i
  fin_cases i <;> rfl

/-- Supporting lemma for MLS p. 250: `K̃_o x = R_ψ K_o R_ψ x`. -/
private lemma rotatedCurvature_mulVec (Ko : Matrix (Fin 2) (Fin 2) ℝ) (ψ : ℝ)
    (x : Fin 2 → ℝ) :
    rotatedCurvature Ko ψ *ᵥ x = angleMatrix ψ *ᵥ (Ko *ᵥ (angleMatrix ψ *ᵥ x)) := by
  simp [rotatedCurvature, mulVec_mulVec, Matrix.mul_assoc]

/-- **The algebraic core of MLS p. 252, "After some algebraic manipulation":** with
`a_f = M_f α̇_f`, `a_o = M_o α̇_o`, `v = (v_x, v_y)` and `w = (−ω_y, ω_x)`, the tangential rows of
(5.37) are equivalent to `(K_f + K̃_o) a_f = w − K̃_o v` and `(K_f + K̃_o) R_ψ a_o = w + K_f v`,
when the relative curvature form is invertible. -/
private lemma tangential_iff (hX : IsUnit (relativeCurvature Kf Ko ψ).det)
    (af ao v w : Fin 2 → ℝ) :
    (af + v = angleMatrix ψ *ᵥ ao ∧ Kf *ᵥ af + -w = -(angleMatrix ψ *ᵥ (Ko *ᵥ ao))) ↔
      (relativeCurvature Kf Ko ψ *ᵥ af = w - rotatedCurvature Ko ψ *ᵥ v ∧
        relativeCurvature Kf Ko ψ *ᵥ (angleMatrix ψ *ᵥ ao) = w + Kf *ᵥ v) := by
  have hX' : ∀ x, relativeCurvature Kf Ko ψ *ᵥ x = Kf *ᵥ x + rotatedCurvature Ko ψ *ᵥ x :=
    fun x => by rw [relativeCurvature, add_mulVec]
  have hRR := angleMatrix_mulVec_mulVec ψ
  constructor
  · rintro ⟨h1, h2⟩
    have e2 : angleMatrix ψ *ᵥ (Ko *ᵥ ao) = rotatedCurvature Ko ψ *ᵥ (af + v) := by
      rw [rotatedCurvature_mulVec, h1, hRR]
    rw [e2, mulVec_add] at h2
    refine ⟨?_, ?_⟩
    · rw [hX']
      linear_combination (norm := module) h2
    · rw [← h1, mulVec_add, hX', hX']
      linear_combination (norm := module) h2
  · rintro ⟨h1, h2⟩
    have hd : relativeCurvature Kf Ko ψ *ᵥ (angleMatrix ψ *ᵥ ao - af) =
        relativeCurvature Kf Ko ψ *ᵥ v := by
      rw [mulVec_sub, h1, h2, hX' v]
      abel
    have hinj : angleMatrix ψ *ᵥ ao - af = v := by
      have := congrArg (fun x => (relativeCurvature Kf Ko ψ)⁻¹ *ᵥ x) hd
      simpa [mulVec_mulVec, nonsing_inv_mul _ hX] using this
    have e1 : af + v = angleMatrix ψ *ᵥ ao := by
      rw [← hinj]
      abel
    refine ⟨e1, ?_⟩
    have e2 : angleMatrix ψ *ᵥ (Ko *ᵥ ao) = rotatedCurvature Ko ψ *ᵥ (af + v) := by
      rw [rotatedCurvature_mulVec, e1, hRR]
    rw [e2, mulVec_add]
    rw [hX'] at h1
    linear_combination (norm := module) h1

/-- **MLS p. 252: "After some algebraic manipulation, we can write equation (5.37) in the form given
by equation (5.28)."** When `M_f`, `M_o` and the relative curvature form `K_f + K̃_o` are invertible
(the last is the hypothesis of p. 251), (5.37) and (5.28) are equivalent. -/
theorem contactEquations_iff_kinematicEquations (hMf : IsUnit Mf.det) (hMo : IsUnit Mo.det)
    (hX : IsUnit (relativeCurvature Kf Ko ψ).det) :
    ContactEquations Mf Kf Mo Ko Tf To ψ αf' αo' ψ' V ↔
      KinematicEquations Mf Kf Mo Ko Tf To ψ αf' αo' ψ' V := by
  have hRR := angleMatrix_mulVec_mulVec ψ
  have key : ∀ z, αo' = Mo⁻¹ *ᵥ (angleMatrix ψ *ᵥ z) ↔ angleMatrix ψ *ᵥ (Mo *ᵥ αo') = z :=
    fun z => by
      rw [eq_inv_mulVec_iff hMo]
      constructor
      · intro h
        rw [h, hRR]
      · intro h
        rw [← h, hRR]
  have hw := vec_neg_swap (V.angular 1) (V.angular 0)
  have core := tangential_iff hX (Mf *ᵥ αf') (Mo *ᵥ αo') ![V.linear 0, V.linear 1]
    ![-V.angular 1, V.angular 0]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := core.mp ⟨h.linear_tangent, by rw [← hw]; exact h.angular_tangent⟩
    refine ⟨?_, ?_, ?_, h.linear_normal⟩
    · rw [eq_inv_mulVec_iff hMf, eq_inv_mulVec_iff hX]
      exact h1
    · rw [key, eq_inv_mulVec_iff hX]
      exact h2
    · linarith [h.angular_normal]
  · intro h
    have h1 := (eq_inv_mulVec_iff hX).mp ((eq_inv_mulVec_iff hMf).mp h.rate_finger)
    have h2 := (eq_inv_mulVec_iff hX).mp ((key _).mp h.rate_object)
    obtain ⟨e1, e2⟩ := core.mpr ⟨h1, h2⟩
    exact ⟨e1, h.normal, by rw [hw]; exact e2, by linarith [h.rate_angle]⟩

/-- **Pure rolling contact (MLS p. 249):** "for pure rolling contact we have `v_x = v_y = 0` and
`ω_z = 0`", for the relative twist `V = V^b_{l_o l_f}`. -/
def IsRolling (V : Twist) : Prop := V.linear 0 = 0 ∧ V.linear 1 = 0 ∧ V.angular 2 = 0

/-- **Pure sliding contact (MLS p. 249):** "for pure sliding contact we have `ω_x = ω_y = ω_z = 0`",
for the relative twist `V = V^b_{l_o l_f}`. -/
def IsSliding (V : Twist) : Prop := V.angular = 0

/-- **MLS Corollary 5.11.1, eq. (5.38), p. 252, the contact coordinates for rolling contact:**
`α̇_f = M_f⁻¹ (K_f + K̃_o)⁻¹ (−ω_y, ω_x)`, `α̇_o = M_o⁻¹ R_ψ (K_f + K̃_o)⁻¹ (−ω_y, ω_x)` and
`ψ̇ = T_f M_f α̇_f + T_o M_o α̇_o`. -/
structure RollingEquations (Mf Kf Mo Ko : Matrix (Fin 2) (Fin 2) ℝ) (Tf To : Fin 2 → ℝ) (ψ : ℝ)
    (αf' αo' : Fin 2 → ℝ) (ψ' : ℝ) (V : Twist) : Prop where
  /-- First line of (5.38). -/
  rate_finger : αf' = Mf⁻¹ *ᵥ ((relativeCurvature Kf Ko ψ)⁻¹ *ᵥ ![-V.angular 1, V.angular 0])
  /-- Second line of (5.38). -/
  rate_object : αo' = Mo⁻¹ *ᵥ (angleMatrix ψ *ᵥ ((relativeCurvature Kf Ko ψ)⁻¹ *ᵥ
    ![-V.angular 1, V.angular 0]))
  /-- Third line of (5.38). -/
  rate_angle : ψ' = Tf ⬝ᵥ (Mf *ᵥ αf') + To ⬝ᵥ (Mo *ᵥ αo')

/-- **MLS Corollary 5.11.1, p. 252: (5.28) under pure rolling gives (5.38).** -/
theorem rollingEquations_of_kinematicEquations
    (h : KinematicEquations Mf Kf Mo Ko Tf To ψ αf' αo' ψ' V) (hr : IsRolling V) :
    RollingEquations Mf Kf Mo Ko Tf To ψ αf' αo' ψ' V := by
  obtain ⟨h0, h1, h2⟩ := hr
  have hv : ![V.linear 0, V.linear 1] = 0 := by
    rw [h0, h1]
    ext i
    fin_cases i <;> simp
  refine ⟨?_, ?_, ?_⟩
  · rw [h.rate_finger, hv, mulVec_zero, sub_zero]
  · rw [h.rate_object, hv, mulVec_zero, add_zero]
  · rw [h.rate_angle, h2, zero_add]

/-- **The derivative-level core of MLS Proposition 5.12, p. 254 ("if the matrix `K_f + R_ψ K_o R_ψᵀ`
is full rank"):** for invertible `M_f`, `M_o`, zero relative velocity forces zero contact rates in
(5.37), for every choice of rates, exactly when the relative curvature form is invertible. So the
linear map from contact rates `(α̇_f, α̇_o, ψ̇)` to relative velocities defined by (5.37) is
injective exactly under the book's rank condition. -/
theorem contactEquations_zero_injective_iff (hMf : IsUnit Mf.det) (hMo : IsUnit Mo.det) :
    (∀ (αf' αo' : Fin 2 → ℝ) (ψ' : ℝ),
        ContactEquations Mf Kf Mo Ko Tf To ψ αf' αo' ψ' 0 → αf' = 0 ∧ αo' = 0 ∧ ψ' = 0) ↔
      IsUnit (relativeCurvature Kf Ko ψ).det := by
  constructor
  · intro H
    by_contra hX
    have hdet : (relativeCurvature Kf Ko ψ).det = 0 := by
      rwa [isUnit_iff_ne_zero, not_not] at hX
    obtain ⟨a, ha, hXa⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hf : Mf *ᵥ (Mf⁻¹ *ᵥ a) = a := by
      rw [mulVec_mulVec, mul_nonsing_inv _ hMf, one_mulVec]
    have ho : Mo *ᵥ (Mo⁻¹ *ᵥ (angleMatrix ψ *ᵥ a)) = angleMatrix ψ *ᵥ a := by
      rw [mulVec_mulVec, mul_nonsing_inv _ hMo, one_mulVec]
    have hK : Kf *ᵥ a + angleMatrix ψ *ᵥ (Ko *ᵥ (angleMatrix ψ *ᵥ a)) = 0 := by
      rw [← rotatedCurvature_mulVec, ← add_mulVec]
      exact hXa
    have hc : ContactEquations Mf Kf Mo Ko Tf To ψ (Mf⁻¹ *ᵥ a)
        (Mo⁻¹ *ᵥ (angleMatrix ψ *ᵥ a)) (Tf ⬝ᵥ a + To ⬝ᵥ (angleMatrix ψ *ᵥ a)) 0 := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hf, ho, angleMatrix_mulVec_mulVec]
        simp [vec_zero_zero]
      · simp
      · rw [hf, ho]
        simp only [Twist.zero_angular, PiLp.zero_apply, neg_zero, vec_zero_zero, add_zero]
        linear_combination (norm := module) hK
      · rw [hf, ho]
        simp
    obtain ⟨h1, -, -⟩ := H _ _ _ hc
    apply ha
    rw [← hf, h1, mulVec_zero]
  · intro hX αf' αo' ψ' hc
    have hk := (contactEquations_iff_kinematicEquations hMf hMo hX).mp hc
    have e1 : αf' = 0 := by
      rw [hk.rate_finger]
      simp [vec_zero_zero]
    have e2 : αo' = 0 := by
      rw [hk.rate_object]
      simp [vec_zero_zero]
    refine ⟨e1, e2, ?_⟩
    rw [hk.rate_angle, e1, e2]
    simp

end Rolling
end RoboLean
