import RoboLean.Nonholonomic.Integrability

/-!
# Integrability with a prescribed regularity of the defining functions (MLS eq. (7.9), p. 326)

**What MLS prints.** A distribution of constant dimension `k` is integrable if near every point
there are smooth functions `h₁, …, h_{n−k}` with linearly independent rows `∂hᵢ/∂q` and
`L_f hᵢ = 0` for every `f ∈ Δ` (eq. (7.9), p. 326); Theorem 7.2 (Frobenius, p. 326) relates this to
involutivity.

**Formalized here.** `IsIntegrableAtOfClass n D q₀` is the library's `IsIntegrableAt D q₀` with the
defining map `h` of class `C^n` instead of `C^∞`; for `n = ∞` the two agree
(`isIntegrableAtOfClass_infty_iff`), a larger class implies a smaller one
(`IsIntegrableAtOfClass.mono`), and the necessity half of Theorem 7.2 holds for every `n ≥ 2`
(`isInvolutiveOn_of_isIntegrableAtOfClass`). The sufficiency half proved in this library
(`Nonholonomic/Frobenius`) gives `C¹` defining maps, because its flows are known to be `C¹` only.

**Conventions.** As `IsIntegrableAt` (Chapter 7, `Integrability`): `h : E → ℝ^p` on an open
neighbourhood `U` of `q₀`, onto derivative and `D q = ker Dh(q)` on `U`.
-/

noncomputable section

open Set Filter Topology VectorField
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **MLS eq. (7.9), p. 326, with defining functions of class `C^n`:** on an open neighbourhood
`U` of `q₀` there are `h = (h₁, …, h_p) : E → ℝ^p` of class `C^n` at every point of `U`, with onto
derivative (independent rows `∂hᵢ/∂q`) and `D q = ker Dh(q)` for `q ∈ U`. MLS asks smooth
functions; `n = ∞` is the library's `IsIntegrableAt`. -/
def IsIntegrableAtOfClass (n : WithTop ℕ∞) (D : E → Submodule ℝ E) (q₀ : E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ q₀ ∈ U ∧ ∃ (p : ℕ) (h : E → Fin p → ℝ),
    (∀ q ∈ U, ContDiffAt ℝ n h q) ∧
      ∀ q ∈ U, Function.Surjective (fderiv ℝ h q) ∧
        D q = LinearMap.ker (fderiv ℝ h q : E →ₗ[ℝ] Fin p → ℝ)

/-- **MLS eq. (7.9), p. 326:** integrability with `C^∞` defining functions is the library's
`IsIntegrableAt`. -/
theorem isIntegrableAtOfClass_infty_iff {D : E → Submodule ℝ E} {q₀ : E} :
    IsIntegrableAtOfClass ∞ D q₀ ↔ IsIntegrableAt D q₀ :=
  Iff.rfl

/-- **MLS eq. (7.9), p. 326:** defining functions of class `C^n` are of class `C^m` for
`m ≤ n`. -/
theorem IsIntegrableAtOfClass.mono {m n : WithTop ℕ∞} {D : E → Submodule ℝ E} {q₀ : E}
    (h : IsIntegrableAtOfClass n D q₀) (hmn : m ≤ n) : IsIntegrableAtOfClass m D q₀ := by
  obtain ⟨U, hU, hq, p, f, hf, hker⟩ := h
  exact ⟨U, hU, hq, p, f, fun q hq => (hf q hq).of_le hmn, hker⟩

/-- **MLS eq. (7.9), p. 326:** an integrable distribution in the library's sense (`C^∞`
defining functions) is integrable with defining functions of every class `C^n`, `n ≤ ∞`. -/
theorem IsIntegrableAt.isIntegrableAtOfClass {D : E → Submodule ℝ E} {q₀ : E}
    (h : IsIntegrableAt D q₀) {n : WithTop ℕ∞} (hn : n ≤ ∞) : IsIntegrableAtOfClass n D q₀ :=
  (isIntegrableAtOfClass_infty_iff.2 h).mono hn

/-- **MLS Theorem 7.2 (Frobenius), p. 326, "only if", for defining functions of class `C^n` with
`n ≥ 2`:** a distribution integrable near every point of an open set `U` with `C^n` defining
functions is involutive on `U`. -/
theorem isInvolutiveOn_of_isIntegrableAtOfClass {n : WithTop ℕ∞} (hn : 2 ≤ n)
    {D : E → Submodule ℝ E} {U : Set E} (hU : IsOpen U)
    (hD : ∀ q ∈ U, IsIntegrableAtOfClass n D q) : IsInvolutiveOn D U := by
  intro f g hf hg hfD hgD q hq
  obtain ⟨V, hV, hqV, p, h, hsmooth, hker⟩ := hD q hq
  have hUV : U ∩ V ∈ 𝓝 q := (hU.inter hV).mem_nhds ⟨hq, hqV⟩
  have hsec : ∀ s : E → E, (∀ x ∈ U, s x ∈ D x) → ∀ᶠ x in 𝓝 q, fderiv ℝ h x (s x) = 0 := by
    intro s hs
    filter_upwards [hUV] with x hx
    have hmem := hs x hx.1
    rw [(hker x hx.2).2] at hmem
    exact hmem
  rw [(hker q hqV).2]
  exact fderiv_lieBracket_eq_zero ((hsmooth q hqV).of_le hn) (hf q hq) (hg q hq) (hsec f hfD)
    (hsec g hgD)

end Nonholonomic
end RoboLean
