import RoboLean.Nonholonomic.Distribution
import RoboLean.Dynamics.ConstrainedLagrangian

/-!
# Integrable distributions and Pfaffian constraints: the necessity half of Frobenius

MLS Chapter 7: integrable distributions (eq. (7.9), printed p. 326), Theorem 7.2 (Frobenius,
p. 326), the annihilating distribution `Δ = Ω^⊥` of a set of Pfaffian constraints (p. 328) and
Proposition 7.4 (p. 328): "A set of smooth Pfaffian constraints is integrable if and only if the
distribution which annihilates the constraints is involutive." The book proves neither Theorem 7.2
nor Proposition 7.4. The nonholonomy of the examples of §3 is "deferred to Section 4" (p. 333).

**Formalized.**

* (7.9) as `IsIntegrableAt D q₀`: near `q₀` there are smooth `h : E → ℝ^p` whose derivative is onto
  (independent rows `∂hᵢ/∂q`) with `D q = ker Dh(q)` (the book's `L_f hᵢ = 0` for `f ∈ Δ`, with
  equality by the dimension count).
* The necessity half, proved: the bracket of two fields annihilated near `q` by `Dh` of a `C²` map
  `h` is annihilated at `q` (`fderiv_lieBracket_eq_zero`, from `L_[f,g] h = L_f L_g h − L_g L_f h`);
  hence an integrable distribution is involutive (`isInvolutiveOn_of_isIntegrableAt`), and a
  Pfaffian constraint `A(q) q̇ = 0` integrable with a `C²` map has an involutive annihilating
  distribution (`IsC2IntegrableOn.isInvolutiveOn`, Proposition 7.4, "only if").
* The sufficiency half of Theorem 7.2 is the named proposition `FrobeniusSufficiency E` for
  finite-dimensional `E` (it is false for every infinite-dimensional `E`): MLS states it without
  proof, and the classical proof uses flows that depend differentiably on their initial state,
  which `Control/FlowDifferentiable` and `Control/FlowCk` supply; the sufficiency half with a `C¹`
  defining map is proved in `FrobeniusFrame`, and the `C^∞` form named here in `FrobeniusSmooth`
  (`frobeniusSufficiency`). `frobenius` is
  the equivalence of Theorem 7.2 under that proposition.
* The contrapositive used for the examples (`not_isC2IntegrableOn_of_lieBracket`): if two
  differentiable fields annihilated by `A` on an open set have a bracket not annihilated at a point
  of it, the constraint is not integrable on that set.

**Conventions.** Pfaffian constraints are the library's `A : ℝⁿ → ℝ^{k×n}` (Chapter 6,
`Constrained.PfaffianAt`); integrability with a `C²` witness (`IsC2IntegrableOn`) is the library's
kernel-equality integrability `Constrained.IsIntegrableOn` with `h` of class `C²` at every point of
the set (MLS: smooth); the book's p. 318 form (`hᵢ(q(t)) = 0 ⇔ ωᵢ(q) q̇ = 0`) is not used.
-/

noncomputable section

open Set Filter Topology VectorField Matrix
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **MLS p. 326 and p. 328 (the necessity half of Proposition 7.4):** if `h` is `C²` at `q` and
the fields `f, g` are differentiable at `q` with `Dh(x) f(x) = 0` and `Dh(x) g(x) = 0` for all `x`
near `q`, then `Dh(q) [f, g](q) = 0`. -/
theorem fderiv_lieBracket_eq_zero {h : E → F} {f g : E → E} {q : E} (hh : ContDiffAt ℝ 2 h q)
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q)
    (hfh : ∀ᶠ x in 𝓝 q, fderiv ℝ h x (f x) = 0) (hgh : ∀ᶠ x in 𝓝 q, fderiv ℝ h x (g x) = 0) :
    fderiv ℝ h q (lieBracket ℝ f g q) = 0 := by
  have h1 : fderiv ℝ (lieDerivative g h) q = 0 := by
    have he : lieDerivative g h =ᶠ[𝓝 q] fun _ => (0 : F) := hgh
    rw [he.fderiv_eq]
    exact fderiv_const_apply 0
  have h2 : fderiv ℝ (lieDerivative f h) q = 0 := by
    have he : lieDerivative f h =ᶠ[𝓝 q] fun _ => (0 : F) := hfh
    rw [he.fderiv_eq]
    exact fderiv_const_apply 0
  have key := lieDerivative_lieBracket hh hf hg
  rw [lieDerivative_apply] at key
  rw [key, lieDerivative_apply, lieDerivative_apply, h1, h2]
  simp

/-- **MLS eq. (7.9), p. 326: `D` is integrable near `q₀`:** on an open neighborhood `U` of `q₀`
there are smooth functions `h = (h₁, …, h_p) : E → ℝ^p` whose derivative is onto at every `q ∈ U`
(the rows `∂hᵢ/∂q` are linearly independent) and `D q = ker Dh(q)` for `q ∈ U`. -/
def IsIntegrableAt (D : E → Submodule ℝ E) (q₀ : E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ q₀ ∈ U ∧ ∃ (p : ℕ) (h : E → Fin p → ℝ),
    (∀ q ∈ U, ContDiffAt ℝ ∞ h q) ∧
      ∀ q ∈ U, Function.Surjective (fderiv ℝ h q) ∧
        D q = LinearMap.ker (fderiv ℝ h q : E →ₗ[ℝ] Fin p → ℝ)

/-- **MLS Theorem 7.2 (Frobenius), p. 326, "only if":** a distribution integrable near every point
of an open set `U` is involutive on `U`. -/
theorem isInvolutiveOn_of_isIntegrableAt {D : E → Submodule ℝ E} {U : Set E} (hU : IsOpen U)
    (hD : ∀ q ∈ U, IsIntegrableAt D q) : IsInvolutiveOn D U := by
  intro f g hf hg hfD hgD q hq
  obtain ⟨V, hV, hqV, p, h, hsmooth, hker⟩ := hD q hq
  have hUV : U ∩ V ∈ 𝓝 q := (hU.inter hV).mem_nhds ⟨hq, hqV⟩
  have hsec : ∀ s : E → E, (∀ x ∈ U, s x ∈ D x) → ∀ᶠ x in 𝓝 q, fderiv ℝ h x (s x) = 0 := by
    intro s hs
    filter_upwards [hUV] with x hx
    have hmem := hs x hx.1
    rw [(hker x hx.2).2] at hmem
    exact hmem
  have h2 : ContDiffAt ℝ 2 h q := (hsmooth q hqV).of_le (by simp)
  rw [(hker q hqV).2]
  exact fderiv_lieBracket_eq_zero h2 (hf q hq) (hg q hq) (hsec f hfD) (hsec g hgD)

/-- **MLS Theorem 7.2 (Frobenius), p. 326, "if", as a named statement, proved in `FrobeniusSmooth` (`frobeniusSufficiency`):** on a
finite-dimensional space (MLS: `ℝⁿ`), every regular involutive distribution spanned by finitely
many smooth fields is integrable near every point. The finite dimension is necessary: with no
generators the distribution is `0` everywhere, regular and involutive, and integrability at a point
gives a linear bijection from `E` onto some `ℝ^p`. -/
def FrobeniusSufficiency (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : Prop :=
  ∀ (m : ℕ) (g : Fin m → E → E), (∀ j, ContDiff ℝ ∞ (g j)) →
    IsRegularOn (spanAt (Set.range g)) Set.univ → IsInvolutiveOn (spanAt (Set.range g)) Set.univ →
      ∀ q, IsIntegrableAt (spanAt (Set.range g)) q

/-- **MLS Theorem 7.2 (Frobenius), p. 326: "A regular distribution is integrable if and only if it
is involutive",** for distributions spanned by finitely many smooth fields, the "if" direction taken
from the named statement `FrobeniusSufficiency E` on a finite-dimensional space (MLS: `ℝⁿ`), which
`FrobeniusSmooth` proves. -/
theorem frobenius [FiniteDimensional ℝ E] (hF : FrobeniusSufficiency E) {m : ℕ} {g : Fin m → E → E}
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) (hreg : IsRegularOn (spanAt (Set.range g)) Set.univ) :
    (∀ q, IsIntegrableAt (spanAt (Set.range g)) q) ↔
      IsInvolutiveOn (spanAt (Set.range g)) Set.univ := by
  exact ⟨fun h => isInvolutiveOn_of_isIntegrableAt isOpen_univ (fun q _ => h q),
    fun hinv => hF m g hg hreg hinv⟩

variable {n k : ℕ}

/-- **MLS p. 328: the distribution annihilating the Pfaffian constraints `A(q) q̇ = 0`,**
`Δ_q = Ω_q^⊥ = ker A(q)`. -/
def annihilator (A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ) (q : Fin n → ℝ) :
    Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (Matrix.mulVecLin (A q))

/-- **MLS p. 328:** `v ∈ Δ_q` exactly when `A(q) v = 0`. -/
theorem mem_annihilator {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ} {q v : Fin n → ℝ} :
    v ∈ annihilator A q ↔ A q *ᵥ v = 0 := by
  rfl

/-- **MLS pp. 267–268 and p. 328: Pfaffian constraints integrable on `Q` with a `C²` map:** some
`h : ℝⁿ → ℝᵏ` of class `C²` at every `q ∈ Q` has `A(q) v = 0 ⇔ (∂h/∂q) v = 0` at every `q ∈ Q`
(the library's kernel-equality integrability with a `C²` witness; MLS: smooth). -/
def IsC2IntegrableOn (A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ) (Q : Set (Fin n → ℝ)) : Prop :=
  ∃ h : (Fin n → ℝ) → Fin k → ℝ, ∀ q ∈ Q, ContDiffAt ℝ 2 h q ∧
    ∀ v, A q *ᵥ v = 0 ↔ MapJacobian.jac h q *ᵥ v = 0

/-- **MLS pp. 267–268:** integrability with a `C²` map is the library's integrability
(`Constrained.IsIntegrableOn`) with a smoother witness. -/
theorem IsC2IntegrableOn.isIntegrableOn {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ}
    {Q : Set (Fin n → ℝ)} (hA : IsC2IntegrableOn A Q) : Constrained.IsIntegrableOn A Q := by
  obtain ⟨h, hh⟩ := hA
  exact ⟨h, fun q hq => ⟨(hh q hq).1.differentiableAt (by norm_num), (hh q hq).2⟩⟩

/-- **MLS Proposition 7.4, p. 328, "only if":** if the Pfaffian constraints `A(q) q̇ = 0` are
integrable on an open set `U` with a `C²` map, the annihilating distribution is involutive on
`U`. -/
theorem IsC2IntegrableOn.isInvolutiveOn {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hA : IsC2IntegrableOn A U) :
    IsInvolutiveOn (annihilator A) U := by
  obtain ⟨h, hh⟩ := hA
  intro f g hf hg hfD hgD q hq
  have hsec : ∀ s : (Fin n → ℝ) → Fin n → ℝ, (∀ x ∈ U, s x ∈ annihilator A x) →
      ∀ᶠ x in 𝓝 q, fderiv ℝ h x (s x) = 0 := by
    intro s hs
    filter_upwards [hU.mem_nhds hq] with x hx
    rw [← MapJacobian.jac_mulVec, ← (hh x hx).2]
    exact mem_annihilator.1 (hs x hx)
  rw [mem_annihilator, (hh q hq).2, MapJacobian.jac_mulVec]
  exact fderiv_lieBracket_eq_zero (hh q hq).1 (hf q hq) (hg q hq) (hsec f hfD) (hsec g hgD)

/-- **MLS p. 333 ("the proof of their nonholonomy … is deferred to Section 4") by Proposition 7.4,
contrapositive:** if `g₁, g₂` are differentiable on an open set `U`, satisfy `A g₁ = A g₂ = 0` on
`U`, and `A(q) [g₁, g₂](q) ≠ 0` at some `q ∈ U`, then the constraints are not integrable on `U`
with any `C²` map. -/
theorem not_isC2IntegrableOn_of_lieBracket {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) {g₁ g₂ : (Fin n → ℝ) → Fin n → ℝ}
    (hg₁ : ∀ x ∈ U, DifferentiableAt ℝ g₁ x) (hg₂ : ∀ x ∈ U, DifferentiableAt ℝ g₂ x)
    (hA₁ : ∀ x ∈ U, A x *ᵥ g₁ x = 0) (hA₂ : ∀ x ∈ U, A x *ᵥ g₂ x = 0) {q : Fin n → ℝ}
    (hq : q ∈ U) (hbr : A q *ᵥ lieBracket ℝ g₁ g₂ q ≠ 0) : ¬ IsC2IntegrableOn A U := by
  intro hint
  exact hbr (mem_annihilator.1 (hint.isInvolutiveOn hU g₁ g₂ hg₁ hg₂
    (fun x hx => mem_annihilator.2 (hA₁ x hx)) (fun x hx => mem_annihilator.2 (hA₂ x hx)) q hq))

end Nonholonomic
end RoboLean
