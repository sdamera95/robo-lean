import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Decay of `exp(tA)` from the eigenvalues of `A` (for MLS Theorem 4.6, printed pp. 184–185)

**What MLS prints (pp. 184–185).** After Theorem 4.6 (stability by
linearization, p. 184), p. 185 states: "If the system (4.37) is time-invariant, then the indirect
method says that if the eigenvalues of `A = ∂f(x)/∂x |_{x=0}` are in the open left half complex
plane, then the origin is asymptotically stable." The linear fact behind it, that `ż = Az` is then
exponentially stable, is not printed; it is proved here and used in
`RoboLean.Control.Linearization`.

**Formalized here.** For a real `n × n` matrix `A` all of whose complex eigenvalues have negative
real part (`IsHurwitz A`) there are `C` and `α > 0` with `‖exp(tA)‖ ≤ C e^{−αt}` for all `t ≥ 0`
(`IsHurwitz.exists_norm_exp_smul_le` for the continuous linear map `x ↦ A x` on `Fin n → ℝ`,
`IsHurwitz.exists_norm_matrix_exp_smul_le` for the matrix). The route:

* (a) the converse spectral mapping inclusion `σ(exp B) ⊆ exp(σ(B))` for a complex square matrix
  `B` (`spectrum_exp_subset`): an eigenvalue `μ` of `exp B` has an eigenspace that `B` maps into
  itself, `B` has an eigenvector `w` there (`ℂ` is algebraically closed), and
  `exp B w = e^λ w` when `B w = λ w` (`exp_mulVec_of_mulVec_eq_smul`, summing the series);
* (b) a corollary of Gelfand's formula: if the spectral radius of `a` is below `r`, then
  `‖aᵏ‖ ≤ C rᵏ` for all `k` (`exists_norm_pow_le_of_spectralRadius_lt`);
* (c) the decay bound, by writing `t = kT + s` with `0 ≤ s ≤ T` and bounding `exp(sb)` on
  `[0, T]` by compactness (`exists_norm_exp_smul_le_of_norm_pow_le`).

The real matrix is moved to `ℂ` entrywise (`Matrix.map` with the coercion `ℝ → ℂ`), which commutes
with `exp` (Mathlib's `NormedSpace.map_exp`) and preserves the norm.

**Conventions.** Vectors are `Fin n → ℝ` with Mathlib's sup norm, as in the rest of
`RoboLean.Control`. A matrix is given the operator norm of that sup norm (Mathlib's
`Matrix.linftyOpNormedRing`, opened with `open scoped Matrix.Norms.Operator`: the largest row sum
of absolute values); it equals the operator norm of the continuous linear map `x ↦ A x`
(Mathlib's `Matrix.linfty_opNorm_eq_opNorm`), which is the norm used for the flow of
`RoboLean.Stability.hasFlow_linear`. "Eigenvalue" means a complex eigenvalue of the real matrix,
`A v = μ v` with `v ∈ ℂⁿ`, `v ≠ 0`. The exponential is Mathlib's `NormedSpace.exp`.

**Mathlib notes (pinned v4.34.1).** Mathlib has only the forward inclusion `spectrum.exp_mem_exp`,
no Schur or Jordan form and no Lyapunov equation; it has Gelfand's formula
(`spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius`), finite matrix spectra
(`Matrix.finite_spectrum`), `Module.End.exists_eigenvalue` and `NormedSpace.map_exp`. A matrix has
no default norm, so the operator norm is opened in the sections that need it; a statement whose
`exp` was elaborated with the plain matrix topology meets the normed one by definitional unfolding
(`exact`), not by rewriting.
-/

noncomputable section

open NormedSpace Filter Topology Matrix

namespace RoboLean
namespace Control

/-! ### Gelfand's formula and the decay of `exp(tb)` in a Banach algebra -/

section Gelfand

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- **A corollary of Gelfand's formula** (step (b) of the eigenvalue criterion of MLS p. 185): in a
complex Banach algebra, if the spectral radius of `a` is less than `r`, then `‖aᵏ‖ ≤ C rᵏ` for every
`k` and some `C ≥ 0`. Mathlib's Gelfand formula gives `‖aᵏ‖^{1/k} → ρ(a)`; the finitely many
powers before the bound takes over are absorbed in `C`. -/
theorem exists_norm_pow_le_of_spectralRadius_lt (a : 𝔸) {r : ℝ}
    (h : spectralRadius ℂ a < ENNReal.ofReal r) :
    ∃ C, 0 ≤ C ∧ ∀ k : ℕ, ‖a ^ k‖ ≤ C * r ^ k := by
  have hr : 0 < r := by
    by_contra hr
    rw [ENNReal.ofReal_of_nonpos (not_lt.mp hr)] at h
    exact ENNReal.not_lt_zero h
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a).eventually_lt_const h)
  have hbig : ∀ k, N + 1 ≤ k → ‖a ^ k‖ ≤ r ^ k := by
    intro k hk
    have h1 := (ENNReal.ofReal_lt_ofReal_iff'.mp (hN k (by omega))).1
    have h2 : (‖a ^ k‖ ^ (1 / k : ℝ)) ^ k = ‖a ^ k‖ := by
      rw [one_div]
      exact Real.rpow_inv_natCast_pow (norm_nonneg _) (by omega)
    rw [← h2]
    exact pow_le_pow_left₀ (by positivity) h1.le k
  have hsum : 0 ≤ ∑ k ∈ Finset.range (N + 1), ‖a ^ k‖ / r ^ k :=
    Finset.sum_nonneg fun k _ => by positivity
  refine ⟨1 + ∑ k ∈ Finset.range (N + 1), ‖a ^ k‖ / r ^ k, by positivity, fun k => ?_⟩
  have hrk : 0 < r ^ k := pow_pos hr k
  rcases lt_or_ge k (N + 1) with hk | hk
  · have h1 : ‖a ^ k‖ / r ^ k ≤ ∑ k ∈ Finset.range (N + 1), ‖a ^ k‖ / r ^ k :=
      Finset.single_le_sum (f := fun k => ‖a ^ k‖ / r ^ k) (fun i _ => by positivity)
        (Finset.mem_range.mpr hk)
    have h2 : ‖a ^ k‖ / r ^ k ≤ 1 + ∑ k ∈ Finset.range (N + 1), ‖a ^ k‖ / r ^ k := by linarith
    rwa [div_le_iff₀ hrk] at h2
  · have := hbig k hk
    nlinarith

end Gelfand

section Split

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **Decay of `exp(tb)` from decay at the multiples of one time step** (step (c) of the eigenvalue
criterion of MLS p. 185): in a real Banach algebra, if `‖exp(Tb)ᵏ‖ ≤ C (e^{−αT})ᵏ` for every `k`,
with `T > 0`, then `‖exp(tb)‖ ≤ K e^{−αt}` for all `t ≥ 0` and some `K`. The proof writes
`t = kT + s` with `0 ≤ s ≤ T`, so `exp(tb) = exp(Tb)ᵏ exp(sb)`, and bounds `exp(sb)` on `[0, T]` by
compactness. -/
theorem exists_norm_exp_smul_le_of_norm_pow_le (b : 𝔸) {T α C : ℝ} (hT : 0 < T)
    (h : ∀ k : ℕ, ‖exp (T • b) ^ k‖ ≤ C * Real.exp (-(α * T)) ^ k) :
    ∃ K, ∀ t : ℝ, 0 ≤ t → ‖exp (t • b)‖ ≤ K * Real.exp (-(α * t)) := by
  let : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hC : 0 ≤ C := by
    have := h 0
    simp only [pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (f := fun s : ℝ => exp (s • b))
    (exp_continuous.comp (continuous_id.smul continuous_const)).continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT.le⟩)
  refine ⟨C * M * Real.exp (|α| * T), fun t ht => ?_⟩
  set k := ⌊t / T⌋₊ with hkdef
  have hk1 : (k : ℝ) * T ≤ t := by
    have := Nat.floor_le (div_nonneg ht hT.le)
    rw [← hkdef] at this
    rwa [le_div_iff₀ hT] at this
  have hk2 : t < ((k : ℝ) + 1) * T := by
    have := Nat.lt_floor_add_one (t / T)
    rw [← hkdef] at this
    rwa [div_lt_iff₀ hT] at this
  set s := t - k * T with hs
  have hs0 : 0 ≤ s := by linarith
  have hsT : s ≤ T := by nlinarith
  have hsplit : exp (t • b) = exp (T • b) ^ k * exp (s • b) := by
    have h1 : t • b = k • (T • b) + s • b := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, ← add_smul, hs]
      ring_nf
    have h2 : Commute (k • (T • b)) (s • b) :=
      (((Commute.refl b).smul_left T).smul_left k).smul_right s
    rw [h1, exp_add_of_commute h2, NormedSpace.exp_nsmul]
  have hexp : Real.exp (-(α * T)) ^ k = Real.exp (-(α * t)) * Real.exp (α * s) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    rw [hs]
    ring
  have hαs : Real.exp (α * s) ≤ Real.exp (|α| * T) := by
    apply Real.exp_le_exp.mpr
    calc α * s ≤ |α| * s := mul_le_mul_of_nonneg_right (le_abs_self α) hs0
      _ ≤ |α| * T := mul_le_mul_of_nonneg_left hsT (abs_nonneg α)
  rw [hsplit]
  calc ‖exp (T • b) ^ k * exp (s • b)‖ ≤ ‖exp (T • b) ^ k‖ * ‖exp (s • b)‖ := norm_mul_le _ _
    _ ≤ (C * Real.exp (-(α * T)) ^ k) * M :=
        mul_le_mul (h k) (hM s ⟨hs0, hsT⟩) (norm_nonneg _) (by positivity)
    _ = C * M * Real.exp (α * s) * Real.exp (-(α * t)) := by rw [hexp]; ring
    _ ≤ C * M * Real.exp (|α| * T) * Real.exp (-(α * t)) := by gcongr

end Split

/-! ### Complex matrices: the converse spectral mapping for `exp` -/

section ComplexMatrix

open scoped Matrix.Norms.Operator

variable {n : ℕ}

/-- **`exp B` acts on an eigenvector of `B` by `e^μ`** (step (a) of the eigenvalue criterion of
MLS p. 185): if `B w = μ w` for a complex square matrix `B`, then `exp(B) w = e^μ w`. The
exponential series of `B` is applied to `w` term by term. -/
theorem exp_mulVec_of_mulVec_eq_smul {B : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ} {w : Fin n → ℂ}
    (h : B *ᵥ w = μ • w) : exp B *ᵥ w = Complex.exp μ • w := by
  have hpow : ∀ k : ℕ, B ^ k *ᵥ w = μ ^ k • w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  have h1 := (exp_series_hasSum_exp' (𝕂 := ℂ) B).map (Matrix.mulVec.addMonoidHomLeft w)
    (continuous_id.matrix_mulVec continuous_const)
  have h2 := (exp_series_hasSum_exp' (𝕂 := ℂ) μ).smul_const w
  rw [← Complex.exp_eq_exp_ℂ] at h2
  refine h1.unique ?_
  convert h2 using 1
  funext k
  simp [Matrix.mulVec.addMonoidHomLeft, Matrix.smul_mulVec, hpow, smul_smul]

/-- **The converse spectral mapping inclusion for the matrix exponential** (step (a) of the
eigenvalue criterion of MLS p. 185): every eigenvalue of `exp B` is `e^λ` for an eigenvalue `λ` of
`B`, for a complex square matrix `B`. Mathlib has only the forward inclusion
(`spectrum.exp_mem_exp`). The proof: `B` commutes with `exp B`, so it maps the eigenspace of `exp B`
for `μ` into itself, and has an eigenvector `w` there; then `μ w = exp(B) w = e^λ w`. -/
theorem spectrum_exp_subset (B : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ (exp B) ⊆ Complex.exp '' spectrum ℂ B := by
  intro μ hμ
  set f := Matrix.toLinAlgEquiv' (exp B) with hf
  set g := Matrix.toLinAlgEquiv' B with hg
  have hμ' : Module.End.HasEigenvalue f μ := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, hf, AlgEquiv.spectrum_eq]
    exact hμ
  have hcomm : Commute f g := by
    have : Commute (exp B) B := (Commute.refl B).exp_left
    simpa [hf, hg] using this.map (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] _)
  have hK : ∀ x ∈ Module.End.eigenspace f μ, g x ∈ Module.End.eigenspace f μ := by
    intro x hx
    have := Module.End.mapsTo_genEigenspace_of_comm hcomm μ 1 hx
    simpa using this
  have : Nontrivial (Module.End.eigenspace f μ) := Submodule.nontrivial_iff_ne_bot.mpr hμ'
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (g.restrict hK)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hw
  have hw0 : (w : Fin n → ℂ) ≠ 0 := by
    intro h0
    exact hw.2 (Subtype.ext h0)
  have hw1 : B *ᵥ (w : Fin n → ℂ) = c • (w : Fin n → ℂ) := by
    have := congrArg Subtype.val hw.1
    simpa [hg, LinearMap.restrict_apply] using this
  have hw2 : exp B *ᵥ (w : Fin n → ℂ) = μ • (w : Fin n → ℂ) := by
    have := Module.End.mem_eigenspace_iff.mp w.2
    simpa [hf] using this
  refine ⟨c, ?_, ?_⟩
  · have : Module.End.HasEigenvalue g c :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr (by simpa [hg] using hw1), hw0⟩
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, hg, AlgEquiv.spectrum_eq] at this
    exact this
  · rw [exp_mulVec_of_mulVec_eq_smul hw1] at hw2
    exact smul_left_injective ℂ hw0 hw2

/-- **The spectral radius of `exp B`** (MLS p. 185): if every eigenvalue `μ` of the complex square
matrix `B` has `Re μ < −α`, then the spectral radius of `exp B` is less than `e^{−α}`, since
`|e^λ| = e^{Re λ}`. -/
theorem spectralRadius_exp_lt {B : Matrix (Fin n) (Fin n) ℂ} {α : ℝ}
    (h : ∀ μ ∈ spectrum ℂ B, μ.re < -α) :
    spectralRadius ℂ (exp B) < ENNReal.ofReal (Real.exp (-α)) := by
  rcases (spectrum ℂ (exp B)).eq_empty_or_nonempty with he | hne
  · rw [spectralRadius_eq_of_unital, he]
    simp [Real.exp_pos]
  · rw [ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le]
    refine spectrum.spectralRadius_lt_of_forall_lt_of_nonempty hne fun z hz => ?_
    obtain ⟨c, hc, rfl⟩ := spectrum_exp_subset B hz
    rw [← NNReal.coe_lt_coe, coe_nnnorm, Complex.norm_exp]
    exact Real.exp_lt_exp.mpr (h c hc)

/-- **Exponential decay of `exp(tB)` for a complex matrix** (MLS p. 185): if every eigenvalue `μ` of
`B` has `Re μ < −α`, then `‖exp(tB)‖ ≤ C e^{−αt}` for all `t ≥ 0`, in the operator norm of the sup
norm (`Matrix.Norms.Operator`). Steps (a)–(c) of the module docstring. -/
theorem exists_norm_exp_smul_le_of_re_lt {B : Matrix (Fin n) (Fin n) ℂ} {α : ℝ}
    (h : ∀ μ ∈ spectrum ℂ B, μ.re < -α) :
    ∃ C, ∀ t : ℝ, 0 ≤ t → ‖exp (t • B)‖ ≤ C * Real.exp (-(α * t)) := by
  obtain ⟨C, -, hpow⟩ := exists_norm_pow_le_of_spectralRadius_lt (exp B) (spectralRadius_exp_lt h)
  refine exists_norm_exp_smul_le_of_norm_pow_le B one_pos (C := C) fun k => ?_
  simp only [one_smul, mul_one]
  exact hpow k

end ComplexMatrix

/-! ### Real matrices: the eigenvalue condition and the decay bound -/

section Hurwitz

variable {n : ℕ}

/-- **Eigenvalues are the spectrum** of a square matrix over a field (used to read the eigenvalue
condition of MLS p. 185 as a condition on the spectrum): `μ` is in the spectrum of `M` if and only
if `M v = μ v` for some `v ≠ 0`. -/
theorem mem_spectrum_iff_exists_mulVec_eq_smul {K : Type*} [Field K] {M : Matrix (Fin n) (Fin n) K}
    {μ : K} : μ ∈ spectrum K M ↔ ∃ v : Fin n → K, v ≠ 0 ∧ M *ᵥ v = μ • v := by
  rw [← AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] _) M,
    ← Module.End.hasEigenvalue_iff_mem_spectrum]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hv
    exact ⟨v, hv.2, by simpa using hv.1⟩
  · rintro ⟨v, hv0, hv⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (by simpa using hv), hv0⟩

/-- **The eigenvalue condition of MLS p. 185:** every complex eigenvalue of the real `n × n` matrix
`A` lies in the open left half complex plane, i.e. `Re μ < 0` whenever `A v = μ v` for some
`v ∈ ℂⁿ`, `v ≠ 0` (`A` acting on `ℂⁿ` entrywise through `ℝ → ℂ`). MLS states it for
`A = ∂f/∂x|_{x=0}`; the name `IsHurwitz` is the standard one in control texts, not MLS's. -/
def IsHurwitz (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (μ : ℂ) (v : Fin n → ℂ), v ≠ 0 → A.map (↑) *ᵥ v = μ • v → μ.re < 0

/-- The eigenvalue condition of MLS p. 185 as a condition on the complex spectrum of `A`. -/
theorem isHurwitz_iff_forall_mem_spectrum {A : Matrix (Fin n) (Fin n) ℝ} :
    IsHurwitz A ↔ ∀ μ ∈ spectrum ℂ (A.map ((↑) : ℝ → ℂ)), μ.re < 0 := by
  simp only [mem_spectrum_iff_exists_mulVec_eq_smul]
  constructor
  · rintro h μ ⟨v, hv0, hv⟩
    exact h μ v hv0 hv
  · intro h μ v hv0 hv
    exact h μ ⟨v, hv0, hv⟩

/-- **A uniform margin** (MLS p. 185): if all eigenvalues of `A` have negative real part, then for
some `α > 0` all of them have real part less than `−α`; the spectrum of a matrix is finite. -/
theorem IsHurwitz.exists_pos_re_lt {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsHurwitz A) :
    ∃ α > 0, ∀ μ ∈ spectrum ℂ (A.map ((↑) : ℝ → ℂ)), μ.re < -α := by
  rcases (spectrum ℂ (A.map ((↑) : ℝ → ℂ))).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, by simp [he]⟩
  · obtain ⟨μ₀, hμ₀, hmax⟩ :=
      Set.exists_max_image _ Complex.re (Matrix.finite_spectrum _) hne
    have h0 := isHurwitz_iff_forall_mem_spectrum.mp hA μ₀ hμ₀
    refine ⟨-μ₀.re / 2, by linarith, fun μ hμ => ?_⟩
    have := hmax μ hμ
    linarith

open scoped Matrix.Norms.Operator in
/-- **Exponential decay of `exp(tA)` from the eigenvalues (the matrix form; for MLS p. 185).** If
every complex eigenvalue of the real matrix `A` has negative real part, then there are `C` and
`α > 0` with `‖exp(tA)‖ ≤ C e^{−αt}` for all `t ≥ 0`. The norm is the operator norm of the sup norm
on `ℝⁿ` (`Matrix.Norms.Operator`, the largest row sum of absolute values). -/
theorem IsHurwitz.exists_norm_matrix_exp_smul_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsHurwitz A) :
    ∃ C α, 0 < α ∧ ∀ t : ℝ, 0 ≤ t → ‖exp (t • A)‖ ≤ C * Real.exp (-(α * t)) := by
  obtain ⟨α, hα, hre⟩ := hA.exists_pos_re_lt
  obtain ⟨C, hC⟩ := exists_norm_exp_smul_le_of_re_lt hre
  refine ⟨C, α, hα, fun t ht => ?_⟩
  have hmap : (exp (t • A)).map ((↑) : ℝ → ℂ) = exp (t • A.map ((↑) : ℝ → ℂ)) := by
    have hsm : t • A.map ((↑) : ℝ → ℂ) = Complex.ofRealHom.mapMatrix (t • A) := by
      ext i j
      simp
    rw [hsm]
    exact NormedSpace.map_exp (RingHom.mapMatrix Complex.ofRealHom)
      (Continuous.matrix_map continuous_id Complex.continuous_ofReal) (t • A)
  have hnorm : ‖(exp (t • A)).map ((↑) : ℝ → ℂ)‖ = ‖exp (t • A)‖ := by
    simp [Matrix.linfty_opNorm_def]
  rw [← hnorm, hmap]
  exact hC t ht

/-- **Exponential decay of `exp(tA)` from the eigenvalues (MLS p. 185), for the flow of `ż = Az`.**
If every complex eigenvalue of the real matrix `A` has negative real part, then for the continuous
linear map `x ↦ A x` on `Fin n → ℝ` (sup norm) there are `C` and `α > 0` with
`‖exp(tA)‖ ≤ C e^{−αt}` for all `t ≥ 0`, in the operator norm. `t ↦ exp(tA) x₀` is the flow of
`ż = Az` (`RoboLean.Stability.hasFlow_linear`). -/
theorem IsHurwitz.exists_norm_exp_smul_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsHurwitz A) :
    ∃ C α, 0 < α ∧ ∀ t : ℝ, 0 ≤ t →
      ‖exp (t • LinearMap.toContinuousLinearMap (Matrix.toLin' A))‖ ≤ C * Real.exp (-(α * t)) := by
  open scoped Matrix.Norms.Operator in
  obtain ⟨C, α, hα, h⟩ := hA.exists_norm_matrix_exp_smul_le
  refine ⟨C, α, hα, fun t ht => ?_⟩
  open scoped Matrix.Norms.Operator in
  let Φ : Matrix (Fin n) (Fin n) ℝ ≃ₐ[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
    Matrix.toLinAlgEquiv'.trans (Module.End.toContinuousLinearMap (Fin n → ℝ))
  open scoped Matrix.Norms.Operator in
  have hΦc : Continuous Φ := Φ.toLinearMap.continuous_of_finiteDimensional
  open scoped Matrix.Norms.Operator in
  have h1 : Φ (exp (t • A)) = exp (t • LinearMap.toContinuousLinearMap (Matrix.toLin' A)) := by
    calc Φ (exp (t • A)) = exp (Φ (t • A)) := NormedSpace.map_exp Φ hΦc (t • A)
      _ = exp (t • LinearMap.toContinuousLinearMap (Matrix.toLin' A)) := by
        rw [map_smul]
        rfl
  open scoped Matrix.Norms.Operator in
  have h2 : ‖Φ (exp (t • A))‖ = ‖exp (t • A)‖ := by
    rw [Matrix.linfty_opNorm_eq_opNorm]
    rfl
  rw [← h1, h2]
  exact h t ht

end Hurwitz

end Control
end RoboLean
