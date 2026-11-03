import RoboLean.LieGroups.MatrixLieGroup
import RoboLean.Geometry.RotationLog

/-!
# The exponential map of a matrix Lie group

MLS Appendix A, §2.3, printed pp. 412–414. For `ξ ∈ T_eG`, the integral curve `φ_ξ` of `X_ξ`
through `e` is a one-parameter subgroup, `φ_ξ(s + t) = φ_ξ(s)φ_ξ(t)`; `exp(ξ) = φ_ξ(1)` and
`exp(ξs) = φ_ξ(s)`; "all connected one-parameter subgroups of `G` are obtained in this way"
(p. 412). `exp` is a local diffeomorphism near `0`, so near `e` there is `log` with
`exp ∘ log = id`, "the inverse of `exp`" (p. 413); Example A.14 gives `log` on `SO(3)` by
`2 cos θ + 1 = trace R` and `ω̂ = (R − Rᵀ)/(2 sin θ)` (p. 414).

Reading. `G` is a set of real square matrices and its Lie algebra is
`RoboLean.LieGroup.matrixLieAlgebra G`; the exponential is the matrix exponential (Example A.10).
A one-parameter subgroup of matrices is a map `φ : ℝ → ℝ^{m×m}` with `φ(0) = I` and
`φ(s + t) = φ(s)φ(t)`; "connected" is read as differentiable at `0` (a continuous one-parameter
subgroup of `GL(n, ℝ)` is differentiable, a fact not used here). For `SO(3)` the local inverse is
stated with the library's principal angle `θ = arccos((trace R − 1)/2)` and the axis of
Example A.14 (`Rotation.genericAxis`): on the open ball `‖ω‖ < π` the logarithm `θ · axis` inverts
`ω ↦ exp(ω̂)`, so the exponential is injective there. The other composition, `exp ∘ log = id`, is
`Rotation.genericAxis_spec` (MLS Proposition 2.5 and eqs. (2.17)–(2.18)); surjectivity of `exp`
onto the compact group `SO(3)` is `Rotation.exists_unit_axis_angle_le_pi`. Operator norm on
matrices for derivatives.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean

namespace LieGroup

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **MLS p. 412: `φ_ξ(t) = exp(tξ)` is a one-parameter subgroup of `G`.** For `A` in the Lie algebra
of `G`, `exp(tA) ∈ G`, `exp(0A) = I`, `exp((s + t)A) = exp(sA) exp(tA)`, and `exp(tA)` is an
integral curve of the left invariant field `X_A(g) = gA`. -/
theorem exp_smul_oneParameterSubgroup (G : Set (Matrix m m ℝ)) (A : Matrix m m ℝ)
    (hA : A ∈ matrixLieAlgebra G) (s t : ℝ) :
    NormedSpace.exp (t • A) ∈ G ∧ NormedSpace.exp ((0 : ℝ) • A) = 1 ∧
      NormedSpace.exp ((s + t) • A) = NormedSpace.exp (s • A) * NormedSpace.exp (t • A) ∧
        HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A)) (NormedSpace.exp (t • A) * A) t := by
  refine ⟨hA t, by rw [zero_smul, NormedSpace.exp_zero], ?_, ?_⟩
  · rw [add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left s).smul_right t)
  · exact hasDerivAt_exp_smul_const (𝕂 := ℝ) A t

/-- **MLS p. 412: `exp` maps the Lie algebra into the group**, `exp(A) = φ_A(1) ∈ G`. -/
theorem exp_mem_of_mem_matrixLieAlgebra (G : Set (Matrix m m ℝ)) (A : Matrix m m ℝ)
    (hA : A ∈ matrixLieAlgebra G) : NormedSpace.exp A ∈ G := by
  simpa using hA 1

/-- MLS p. 412, `exp(ξs) = φ_ξ(s)`: the line `ξs` through an element of the Lie algebra stays in
the Lie algebra. -/
theorem smul_mem_matrixLieAlgebra (G : Set (Matrix m m ℝ)) (A : Matrix m m ℝ)
    (hA : A ∈ matrixLieAlgebra G) (c : ℝ) : c • A ∈ matrixLieAlgebra G := by
  intro t
  simpa [smul_smul] using hA (t * c)

/-- **MLS p. 412: every one-parameter subgroup is obtained from the exponential.** A map
`φ : ℝ → ℝ^{m×m}` with `φ(0) = I`, `φ(s + t) = φ(s)φ(t)` and derivative `A` at `0` is
`φ(t) = exp(tA)`. -/
theorem eq_exp_smul_of_oneParameterSubgroup (φ : ℝ → Matrix m m ℝ) (A : Matrix m m ℝ)
    (h0 : φ 0 = 1) (hadd : ∀ s t, φ (s + t) = φ s * φ t) (hA : HasDerivAt φ A 0) (t : ℝ) :
    φ t = NormedSpace.exp (t • A) := by
  have hcomm : ∀ s, φ s * A = A * φ s := by
    intro s
    have hl : HasDerivAt (fun h => φ s * φ h) (φ s * A) 0 := hA.const_mul (φ s)
    have hr : HasDerivAt (fun h => φ h * φ s) (A * φ s) 0 := hA.mul_const (φ s)
    have hfun : (fun h => φ s * φ h) = fun h => φ h * φ s := by
      funext h
      rw [← hadd, ← hadd, add_comm]
    rw [hfun] at hl
    exact hl.unique hr
  have hderiv : ∀ s, HasDerivAt φ (φ s * A) s := by
    intro s
    have h1 : HasDerivAt (fun h => φ s * φ h) (φ s * A) (s - s) := by
      rw [sub_self]
      exact hA.const_mul (φ s)
    have h2 := h1.comp_sub_const s s
    have hfun : (fun x => φ s * φ (x - s)) = φ := by
      funext x
      rw [← hadd, add_sub_cancel]
    rw [hfun] at h2
    exact h2
  let ψ : ℝ → Matrix m m ℝ := fun s => NormedSpace.exp (s • -A) * φ s
  have hψ : ∀ s, HasDerivAt ψ 0 s := by
    intro s
    have he : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -A))
        (NormedSpace.exp (s • -A) * -A) s := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) s
    have h := he.mul (hderiv s)
    have hzero : NormedSpace.exp (s • -A) * -A * φ s + NormedSpace.exp (s • -A) * (φ s * A) = 0 := by
      rw [hcomm s, Matrix.mul_assoc, ← Matrix.mul_add, Matrix.neg_mul, neg_add_cancel,
        Matrix.mul_zero]
    rw [hzero] at h
    exact h
  have hconst : ψ t = ψ 0 :=
    is_const_of_deriv_eq_zero (fun s => (hψ s).differentiableAt) (fun s => (hψ s).deriv) t 0
  have hψ0 : ψ 0 = 1 := by
    simp only [ψ, zero_smul, NormedSpace.exp_zero, h0, Matrix.one_mul]
  have hinv : NormedSpace.exp (t • A) * NormedSpace.exp (t • -A) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl A).neg_right.smul_left t).smul_right t),
      smul_neg, add_neg_cancel, NormedSpace.exp_zero]
  calc φ t = NormedSpace.exp (t • A) * ψ t := by
        simp only [ψ, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    _ = NormedSpace.exp (t • A) := by rw [hconst, hψ0, Matrix.mul_one]

/-- MLS p. 412: the derivative at `0` of a one-parameter subgroup with values in `G` (as in
`eq_exp_smul_of_oneParameterSubgroup`) lies in the Lie algebra of `G`. -/
theorem mem_matrixLieAlgebra_of_oneParameterSubgroup (G : Set (Matrix m m ℝ))
    (φ : ℝ → Matrix m m ℝ) (A : Matrix m m ℝ) (h0 : φ 0 = 1)
    (hadd : ∀ s t, φ (s + t) = φ s * φ t) (hA : HasDerivAt φ A 0) (hG : ∀ t, φ t ∈ G) :
    A ∈ matrixLieAlgebra G := by
  intro t
  rw [← eq_exp_smul_of_oneParameterSubgroup φ A h0 hadd hA t]
  exact hG t

/-- **MLS p. 413 with Example A.14, p. 414: `log ∘ exp = id` on `SO(3)` near the identity.** For
`‖ω‖ < π`, the principal angle `θ` of `R = exp(ω̂)` (`2 cos θ + 1 = trace R`) times the axis
`(R − Rᵀ)^∨/(2 sin θ)` recovers `ω` (for `ω = 0` the angle is `0`). -/
theorem principalAngle_smul_genericAxis_exp (ω : Vec3) (hω : ‖ω‖ < Real.pi) :
    Rotation.principalAngle (Rotation.exp ω 1) • Rotation.genericAxis (Rotation.exp ω 1) = ω := by
  rcases eq_or_ne ω 0 with rfl | hω0
  · have h1 : Rotation.principalAngle (Rotation.exp 0 1) = 0 := by
      show Real.arccos ((Matrix.trace (Rotation.exp 0 1).val - 1) / 2) = 0
      simp
      norm_num
    rw [h1, zero_smul]
  · have hr : 0 < ‖ω‖ := norm_pos_iff.mpr hω0
    set u : Vec3 := ‖ω‖⁻¹ • ω with hu_def
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
    have hωu : ω = ‖ω‖ • u := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hexp : Rotation.exp ω 1 = Rotation.exp u ‖ω‖ := by
      conv_lhs => rw [hωu]
      rw [Rotation.exp_smul, one_mul]
    have hθ : Rotation.principalAngle (Rotation.exp ω 1) = ‖ω‖ := by
      rw [hexp]
      exact Rotation.arccos_trace_exp_of_mem_Icc u hu ‖ω‖ hr.le hω.le
    have hsin : Real.sin ‖ω‖ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hr hω).ne'
    have haxis : Rotation.genericAxis (Rotation.exp ω 1) = u := by
      unfold Rotation.genericAxis
      rw [hθ, hexp]
      exact Rotation.axis_recovery_of_sin_ne_zero u hu ‖ω‖ hsin
    rw [hθ, haxis, ← hωu]

/-- MLS p. 413: the exponential `ω ↦ exp(ω̂)` of `so(3)` is injective on the open ball `‖ω‖ < π`,
where Example A.14's logarithm is its inverse. -/
theorem injOn_rotation_exp_ball :
    Set.InjOn (fun ω : Vec3 => Rotation.exp ω 1) (Metric.ball 0 Real.pi) := by
  intro ω₁ h₁ ω₂ h₂ heq
  simp only at heq
  rw [← principalAngle_smul_genericAxis_exp ω₁ (mem_ball_zero_iff.mp h₁), heq,
    principalAngle_smul_genericAxis_exp ω₂ (mem_ball_zero_iff.mp h₂)]

end LieGroup

end RoboLean
