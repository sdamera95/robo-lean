import RoboLean.Grasp.GeometricParameters

/-!
# Orthogonal charts and lines of curvature (MLS Theorem 5.9)

MLS Chapter 5, §6.1, printed p. 244: "A coordinate chart is an orthogonal coordinate chart if `c_u`
and `c_v` are orthogonal. **Theorem 5.9.** Locally, there exists an orthogonal chart for all regular
surfaces. The proof can be found in any standard book on differential geometry." The curvature
tensor is (5.21), p. 245.

**Theorem 5.9 is recorded as a named statement** (`OrthogonalChartStatement`) and proved in
`OrthogonalChartProof` (`orthogonalChartStatement`): for a smooth chart with injective
differential, every parameter has a neighbourhood that a smooth injective reparametrization makes
orthogonal. The classical proofs rectify two transverse line fields at once (the lines of
curvature away from umbilics, or a coordinate line field and its orthogonal field); the proof in
`OrthogonalChartProof` rectifies one field orthogonal to the first coordinate lines by its smooth
flow (`Control/FlowCk`), keeping the second coordinate, so that no umbilic is excluded.

**Proved here, without flows.**

* A chart whose coordinate lines are lines of curvature (Rodrigues' formula `n_u = κ₁ c_u`,
  `n_v = κ₂ c_v`) with distinct principal curvatures `κ₁ ≠ κ₂` is orthogonal at that point
  (`isOrthogonalAt_of_lines_of_curvature`), and on an open set it is an orthogonal chart
  (`isOrthogonalChartOn_of_lines_of_curvature`); its curvature tensor is then `diag(κ₁, κ₂)`
  (`curvatureTensor_of_lines_of_curvature`). This is the step of the classical proof that turns
  lines of curvature into an orthogonal chart, and it is where umbilics are excluded.
* Away from umbilics the principal directions form a frame as smooth as the curvature tensor: for a
  symmetric `2 × 2` matrix field `S` of class `C^k` near a point where `S` is not a multiple of the
  identity, there are a neighbourhood, `C^k` eigenvalues `λ₁ ≠ λ₂` and a `C^k` unit vector field
  `e` with `S e = λ₁ e` and `S (J e) = λ₂ (J e)`, `J e = (−e₂, e₁)`
  (`exists_principalFrame`). Applied to the curvature tensor of an orthogonal chart, whose entries
  are the shape operator in the orthonormal Gauss frame (5.23), `e` and `J e` are the coordinates of
  the two principal directions in that frame.

An umbilic of an orthogonal chart is a point where `K` is a multiple of the identity
(`IsUmbilicAt`); the book does not use the word.
-/

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace RoboLean
namespace Surface

variable {c : (Fin 2 → ℝ) → Vec3} {α : Fin 2 → ℝ}

/-- **MLS Theorem 5.9, p. 244, as a named statement, proved in `OrthogonalChartProof`:** "Locally, there exists an
orthogonal chart for all regular surfaces." For a chart `c` smooth on an open `U` with injective
differential, every `α₀ ∈ U` is the image of a point `β₀` of an open `V` under a smooth
reparametrization `φ : V → U`, injective on `V`, with `φ(V)` a neighbourhood of `α₀`, such that
`c ∘ φ` is an orthogonal chart on `V`. -/
def OrthogonalChartStatement : Prop :=
  ∀ (c : (Fin 2 → ℝ) → Vec3) (U : Set (Fin 2 → ℝ)), IsOpen U → ContDiffOn ℝ ∞ c U →
    (∀ α ∈ U, Function.Injective (fderiv ℝ c α)) → ∀ α₀ ∈ U,
      ∃ (V : Set (Fin 2 → ℝ)) (φ : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (β₀ : Fin 2 → ℝ),
        β₀ ∈ V ∧ φ β₀ = α₀ ∧ ContDiffOn ℝ ∞ φ V ∧ Set.InjOn φ V ∧ Set.MapsTo φ V U ∧
          φ '' V ∈ 𝓝 α₀ ∧ IsOrthogonalChartOn (c ∘ φ) V

/-- **An umbilic of an orthogonal chart (for MLS Theorem 5.9, p. 244, and eq. (5.21), p. 245):** a
point where the curvature tensor is a multiple of the identity, `K₁₂ = 0` and `K₁₁ = K₂₂`. -/
def IsUmbilicAt (c : (Fin 2 → ℝ) → Vec3) (α : Fin 2 → ℝ) : Prop :=
  curvatureTensor c α 0 1 = 0 ∧ curvatureTensor c α 0 0 = curvatureTensor c α 1 1

/-- `c_uᵀ n_v = c_vᵀ n_u` (supporting lemma for MLS eq. (5.20), p. 245), from the symmetry of the
curvature tensor. -/
private theorem inner_partialU_partialV_gaussNormal (hc : ContDiffAt ℝ 2 c α)
    (h0 : Vec3.cross (partialU c α) (partialV c α) ≠ 0) :
    inner ℝ (partialU c α) (partialV (gaussNormal c) α) =
      inner ℝ (partialV c α) (partialU (gaussNormal c) α) := by
  have hu : partialU c α ≠ 0 := fun h => h0 (by rw [h]; exact Vec3.zero_cross _)
  have hv : partialV c α ≠ 0 := fun h => h0 (by rw [h]; exact Vec3.cross_zero _)
  have hT := congrFun (congrFun (curvatureTensor_transpose hc h0) 0) 1
  simp only [transpose_apply, curvatureTensor, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one] at hT
  have hn : ‖partialU c α‖ * ‖partialV c α‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr hu) (norm_ne_zero_iff.mpr hv)
  field_simp at hT
  exact hT.symm

/-- **Coordinate lines along lines of curvature with distinct principal curvatures give an
orthogonal chart (for MLS Theorem 5.9, p. 244):** if `c` is twice continuously differentiable at
`α` with `c_u × c_v ≠ 0`, and Rodrigues' formula holds along both coordinate directions,
`n_u = κ₁ c_u` and `n_v = κ₂ c_v` with `κ₁ ≠ κ₂`, then `c_u ⟂ c_v`. -/
theorem isOrthogonalAt_of_lines_of_curvature (hc : ContDiffAt ℝ 2 c α)
    (h0 : Vec3.cross (partialU c α) (partialV c α) ≠ 0) {κ₁ κ₂ : ℝ}
    (h1 : partialU (gaussNormal c) α = κ₁ • partialU c α)
    (h2 : partialV (gaussNormal c) α = κ₂ • partialV c α) (hne : κ₁ ≠ κ₂) :
    IsOrthogonalAt c α := by
  have key := inner_partialU_partialV_gaussNormal hc h0
  rw [h1, h2, inner_smul_right, inner_smul_right] at key
  have e : inner ℝ (partialV c α) (partialU c α) = inner ℝ (partialU c α) (partialV c α) :=
    real_inner_comm _ _
  simp only [e] at key
  have : (κ₂ - κ₁) * inner ℝ (partialU c α) (partialV c α) = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne.symm)

/-- **A chart along lines of curvature without umbilics is an orthogonal chart (MLS pp. 243–244,
for Theorem 5.9):** on an open `U` where `c` is twice continuously differentiable with injective
differential, if at every point `n_u = κ₁ c_u` and `n_v = κ₂ c_v` with `κ₁ ≠ κ₂`, then
`IsOrthogonalChartOn c U`. -/
theorem isOrthogonalChartOn_of_lines_of_curvature {U : Set (Fin 2 → ℝ)} (hU : IsOpen U)
    (hc : ContDiffOn ℝ 2 c U) (hinj : ∀ α ∈ U, Function.Injective (fderiv ℝ c α))
    {κ₁ κ₂ : (Fin 2 → ℝ) → ℝ}
    (h1 : ∀ α ∈ U, partialU (gaussNormal c) α = κ₁ α • partialU c α)
    (h2 : ∀ α ∈ U, partialV (gaussNormal c) α = κ₂ α • partialV c α)
    (hne : ∀ α ∈ U, κ₁ α ≠ κ₂ α) : IsOrthogonalChartOn c U := by
  refine ⟨hU, hc, hinj, fun α hα => ?_⟩
  have hcα : ContDiffAt ℝ 2 c α := hc.contDiffAt (hU.mem_nhds hα)
  refine isOrthogonalAt_of_lines_of_curvature hcα ?_ (h1 α hα) (h2 α hα) (hne α hα)
  intro h0
  have hl : LinearIndependent ℝ ![WithLp.ofLp (partialU c α), WithLp.ofLp (partialV c α)] := by
    refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
    have hst' : s • partialU c α + t • partialV c α = 0 := by
      apply WithLp.ofLp_injective
      simpa using hst
    have : fderiv ℝ c α ![s, t] = 0 := by
      rw [fderiv_apply_eq]
      simpa using hst'
    have h := hinj α hα (this.trans (map_zero _).symm)
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  refine crossProduct_ne_zero_iff_linearIndependent.mpr hl ?_
  have := congrArg WithLp.ofLp h0
  simpa [Vec3.cross] using this

/-- **The curvature tensor along lines of curvature (MLS eq. (5.21), p. 245):** for an orthogonal
chart point with `c_u, c_v ≠ 0` where `n_u = κ₁ c_u` and `n_v = κ₂ c_v`, `K = diag(κ₁, κ₂)`. -/
theorem curvatureTensor_of_lines_of_curvature (h : IsOrthogonalAt c α) (hu : partialU c α ≠ 0)
    (hv : partialV c α ≠ 0) {κ₁ κ₂ : ℝ} (h1 : partialU (gaussNormal c) α = κ₁ • partialU c α)
    (h2 : partialV (gaussNormal c) α = κ₂ • partialV c α) :
    curvatureTensor c α = !![κ₁, 0; 0, κ₂] := by
  have h' : inner ℝ (partialV c α) (partialU c α) = 0 := by rw [real_inner_comm]; exact h
  have hu' : ‖partialU c α‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hv' : ‖partialV c α‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [curvatureTensor, h1, h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inner_smul_right, show inner ℝ (partialU c α)
      (partialV c α) = 0 from h, h'] <;> field_simp

/-! ### The principal frame away from umbilics -/

section PrincipalFrame

variable {n : WithTop ℕ∞} {S : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ} {U : Set (Fin 2 → ℝ)}

/-- The quarter turn `J (e₁, e₂) = (−e₂, e₁)` of the plane (supporting definition for the principal
frame, MLS p. 245: the second axis of an orthonormal frame of the tangent plane). -/
def quarterTurn (e : Fin 2 → ℝ) : Fin 2 → ℝ := ![-e 1, e 0]

/-- The half-discriminant `((S₁₁ − S₂₂)/2)² + S₁₂²` of a `2 × 2` matrix (supporting definition for
the principal curvatures of MLS eq. (5.21), p. 245); it vanishes exactly at umbilics. -/
def halfDiscriminant (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := ((A 0 0 - A 1 1) / 2) ^ 2 + A 0 1 ^ 2

private lemma eigen_of_vec {A : Matrix (Fin 2) (Fin 2) ℝ} (hsym : A 0 1 = A 1 0) {l : ℝ}
    (hl : l ^ 2 - (A 0 0 + A 1 1) * l + (A 0 0 * A 1 1 - A 0 1 ^ 2) = 0) :
    A *ᵥ ![A 0 1, l - A 0 0] = l • ![A 0 1, l - A 0 0] ∧
      A *ᵥ ![l - A 1 1, A 0 1] = l • ![l - A 1 1, A 0 1] := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ← hsym] <;>
    first
      | ring1
      | linear_combination -hl

private lemma eigen_quarterTurn {A : Matrix (Fin 2) (Fin 2) ℝ} (hsym : A 0 1 = A 1 0) {l : ℝ}
    {e : Fin 2 → ℝ} (he : A *ᵥ e = l • e) :
    A *ᵥ quarterTurn e = (A 0 0 + A 1 1 - l) • quarterTurn e := by
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  funext i
  fin_cases i <;> simp [quarterTurn, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    first
      | linear_combination h1
      | linear_combination h1 + e 0 * hsym
      | linear_combination -h1
      | linear_combination 2 * h1
      | linear_combination -h0 + e 1 * hsym

private lemma charpoly_root (A : Matrix (Fin 2) (Fin 2) ℝ) (hD : 0 ≤ halfDiscriminant A) :
    ((A 0 0 + A 1 1) / 2 + √(halfDiscriminant A)) ^ 2 -
        (A 0 0 + A 1 1) * ((A 0 0 + A 1 1) / 2 + √(halfDiscriminant A)) +
      (A 0 0 * A 1 1 - A 0 1 ^ 2) = 0 := by
  have h := Real.sq_sqrt hD
  unfold halfDiscriminant at h ⊢
  linear_combination h

/-- **The principal frame away from umbilics (for MLS Theorem 5.9, p. 244, and eqs. (5.21), (5.23),
p. 245):** let `S` be a field of symmetric `2 × 2` matrices whose entries are `C^n` on an open `U`,
and `α₀ ∈ U` a point where `S` is not a multiple of the identity. Then there are an open
neighbourhood `V ⊆ U` of `α₀`, `C^n` functions `λ₁, λ₂` with `λ₁ ≠ λ₂` on `V`, and a `C^n` field
`e` of unit vectors on `V` with `S e = λ₁ e` and `S (J e) = λ₂ (J e)`, `J e = (−e₂, e₁)`. For the
curvature tensor of an orthogonal chart, `λ₁, λ₂` are the principal curvatures and `e`, `J e` the
principal directions in the normalized Gauss frame. -/
theorem exists_principalFrame (hU : IsOpen U) (hS : ∀ i j, ContDiffOn ℝ n (fun α => S α i j) U)
    (hsym : ∀ α, S α 0 1 = S α 1 0) {α₀ : Fin 2 → ℝ} (hα₀ : α₀ ∈ U)
    (hnu : ¬(S α₀ 0 1 = 0 ∧ S α₀ 0 0 = S α₀ 1 1)) :
    ∃ V : Set (Fin 2 → ℝ), IsOpen V ∧ α₀ ∈ V ∧ V ⊆ U ∧
      ∃ (l₁ l₂ : (Fin 2 → ℝ) → ℝ) (e : (Fin 2 → ℝ) → Fin 2 → ℝ),
        ContDiffOn ℝ n l₁ V ∧ ContDiffOn ℝ n l₂ V ∧ ContDiffOn ℝ n e V ∧
        ∀ α ∈ V, e α ⬝ᵥ e α = 1 ∧ S α *ᵥ e α = l₁ α • e α ∧
          S α *ᵥ quarterTurn (e α) = l₂ α • quarterTurn (e α) ∧ l₁ α ≠ l₂ α := by
  set D : (Fin 2 → ℝ) → ℝ := fun α => halfDiscriminant (S α) with hDdef
  have hDc : ContDiffOn ℝ n D U := by
    simp only [hDdef, halfDiscriminant]
    exact (((hS 0 0).sub (hS 1 1)).div_const 2).pow 2 |>.add ((hS 0 1).pow 2)
  have hD0 : 0 < D α₀ := by
    simp only [hDdef, halfDiscriminant]
    by_contra hle
    push Not at hle
    have h1 : S α₀ 0 1 = 0 := by nlinarith [sq_nonneg ((S α₀ 0 0 - S α₀ 1 1) / 2), sq_nonneg (S α₀ 0 1)]
    have h2 : S α₀ 0 0 = S α₀ 1 1 := by nlinarith [sq_nonneg ((S α₀ 0 0 - S α₀ 1 1) / 2), sq_nonneg (S α₀ 0 1)]
    exact hnu ⟨h1, h2⟩
  set V₁ := U ∩ {α | 0 < D α} with hV₁
  have hV₁o : IsOpen V₁ := hDc.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  have hV₁U : V₁ ⊆ U := Set.inter_subset_left
  set l₁ : (Fin 2 → ℝ) → ℝ := fun α => (S α 0 0 + S α 1 1) / 2 + √(D α) with hl₁
  set l₂ : (Fin 2 → ℝ) → ℝ := fun α => (S α 0 0 + S α 1 1) / 2 - √(D α) with hl₂
  have hsq : ContDiffOn ℝ n (fun α => √(D α)) V₁ :=
    (hDc.mono hV₁U).sqrt fun α hα => hα.2.ne'
  have hl₁c : ContDiffOn ℝ n l₁ V₁ :=
    (((hS 0 0).add (hS 1 1)).div_const 2).mono hV₁U |>.add hsq
  have hl₂c : ContDiffOn ℝ n l₂ V₁ :=
    (((hS 0 0).add (hS 1 1)).div_const 2).mono hV₁U |>.sub hsq
  have hroot : ∀ α, l₁ α ^ 2 - (S α 0 0 + S α 1 1) * l₁ α + (S α 0 0 * S α 1 1 - S α 0 1 ^ 2) = 0 :=
    fun α => charpoly_root (S α) (by simp only [halfDiscriminant]; positivity)
  have hl₂eq : ∀ α, l₂ α = S α 0 0 + S α 1 1 - l₁ α := fun α => by simp only [hl₁, hl₂]; ring
  have hne : ∀ α ∈ V₁, l₁ α ≠ l₂ α := fun α hα => by
    have := Real.sqrt_pos.mpr hα.2
    simp only [hl₁, hl₂]
    linarith
  -- the eigenvector formula: one of two, nonzero at `α₀`
  have key : ∀ u : (Fin 2 → ℝ) → Fin 2 → ℝ, ContDiffOn ℝ n u V₁ → u α₀ ≠ 0 →
      (∀ α, S α *ᵥ u α = l₁ α • u α) →
      ∃ V : Set (Fin 2 → ℝ), IsOpen V ∧ α₀ ∈ V ∧ V ⊆ U ∧
        ∃ (l₁ l₂ : (Fin 2 → ℝ) → ℝ) (e : (Fin 2 → ℝ) → Fin 2 → ℝ),
          ContDiffOn ℝ n l₁ V ∧ ContDiffOn ℝ n l₂ V ∧ ContDiffOn ℝ n e V ∧
          ∀ α ∈ V, e α ⬝ᵥ e α = 1 ∧ S α *ᵥ e α = l₁ α • e α ∧
            S α *ᵥ quarterTurn (e α) = l₂ α • quarterTurn (e α) ∧ l₁ α ≠ l₂ α := by
    intro u hu hu0 heig
    have hN : ContDiffOn ℝ n (fun α => u α ⬝ᵥ u α) V₁ := by
      have h0 : ContDiffOn ℝ n (fun α => u α 0) V₁ := (contDiffOn_pi.mp hu) 0
      have h1 : ContDiffOn ℝ n (fun α => u α 1) V₁ := (contDiffOn_pi.mp hu) 1
      simp only [dotProduct, Fin.sum_univ_two]
      exact (h0.mul h0).add (h1.mul h1)
    set V := V₁ ∩ {α | 0 < u α ⬝ᵥ u α} with hV
    have hVo : IsOpen V := hN.continuousOn.isOpen_inter_preimage hV₁o isOpen_Ioi
    have hpos : 0 < u α₀ ⬝ᵥ u α₀ := by
      have : u α₀ ⬝ᵥ u α₀ = u α₀ 0 ^ 2 + u α₀ 1 ^ 2 := by
        simp [dotProduct, Fin.sum_univ_two, pow_two]
      rw [this]
      by_contra hle
      push Not at hle
      apply hu0
      funext i
      fin_cases i <;> simp <;> nlinarith [sq_nonneg (u α₀ 0), sq_nonneg (u α₀ 1)]
    have hα₀V : α₀ ∈ V := ⟨⟨hα₀, hD0⟩, hpos⟩
    have hVV₁ : V ⊆ V₁ := Set.inter_subset_left
    refine ⟨V, hVo, hα₀V, hVV₁.trans hV₁U, l₁, l₂, fun α => (√(u α ⬝ᵥ u α))⁻¹ • u α,
      hl₁c.mono hVV₁, hl₂c.mono hVV₁, ?_, fun α hα => ?_⟩
    · exact ((hN.mono hVV₁).sqrt fun α hα => hα.2.ne').inv
        (fun α hα => (Real.sqrt_pos.mpr hα.2).ne') |>.smul (hu.mono hVV₁)
    · have hs := Real.sqrt_pos.mpr hα.2
      have he : S α *ᵥ ((√(u α ⬝ᵥ u α))⁻¹ • u α) = l₁ α • ((√(u α ⬝ᵥ u α))⁻¹ • u α) := by
        rw [Matrix.mulVec_smul, heig, smul_comm]
      refine ⟨?_, he, ?_, hne α (hVV₁ hα)⟩
      · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
          ← mul_inv, Real.mul_self_sqrt hα.2.le, inv_mul_cancel₀ hα.2.ne']
      · rw [eigen_quarterTurn (hsym α) he, hl₂eq]
  by_cases hcase : S α₀ 0 1 ≠ 0 ∨ S α₀ 0 0 < S α₀ 1 1
  · refine key (fun α => ![S α 0 1, l₁ α - S α 0 0]) ?_ ?_ ?_
    · refine contDiffOn_pi.mpr fun i => ?_
      fin_cases i
      · simpa using (hS 0 1).mono hV₁U
      · simpa using hl₁c.sub ((hS 0 0).mono hV₁U)
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp at h0 h1
      rcases hcase with hq | hpr
      · exact hq h0
      · have hD : D α₀ = ((S α₀ 0 0 - S α₀ 1 1) / 2) ^ 2 := by
          simp only [hDdef, halfDiscriminant, h0]
          ring
        have : √(D α₀) = (S α₀ 1 1 - S α₀ 0 0) / 2 := by
          rw [hD, show ((S α₀ 0 0 - S α₀ 1 1) / 2) ^ 2 = ((S α₀ 1 1 - S α₀ 0 0) / 2) ^ 2 by ring,
            Real.sqrt_sq (by linarith)]
        simp only [hl₁, this] at h1
        linarith
    · exact fun α => (eigen_of_vec (hsym α) (hroot α)).1
  · push Not at hcase
    obtain ⟨hq, hpr⟩ := hcase
    have hlt : S α₀ 1 1 < S α₀ 0 0 :=
      lt_of_le_of_ne hpr fun h => hnu ⟨hq, h.symm⟩
    refine key (fun α => ![l₁ α - S α 1 1, S α 0 1]) ?_ ?_ ?_
    · refine contDiffOn_pi.mpr fun i => ?_
      fin_cases i
      · simpa using hl₁c.sub ((hS 1 1).mono hV₁U)
      · simpa using (hS 0 1).mono hV₁U
    · intro h
      have h0 := congrFun h 0
      simp at h0
      have hD : D α₀ = ((S α₀ 0 0 - S α₀ 1 1) / 2) ^ 2 := by
        simp only [hDdef, halfDiscriminant, hq]
        ring
      have : √(D α₀) = (S α₀ 0 0 - S α₀ 1 1) / 2 := by
        rw [hD, Real.sqrt_sq (by linarith)]
      simp only [hl₁, this] at h0
      linarith
    · exact fun α => (eigen_of_vec (hsym α) (hroot α)).2

end PrincipalFrame

end Surface
end RoboLean
