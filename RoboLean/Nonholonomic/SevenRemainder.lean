import RoboLean.Nonholonomic.SevenRemainderFields
import RoboLean.Nonholonomic.Controllability
import RoboLean.Nonholonomic.VectorField
import RoboLean.Nonholonomic.FiltrationBrackets
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Pfaffian constraints, integrating factors, codistributions and integrals of the constraints

MLS Chapter 7, printed pp. 318–320, 327–328 and 339–341: the items of §§7.1–7.4 that state a
checkable result and that the rows on vector fields, distributions, Frobenius' theorem and the
filtration do not cover.

* **The involutive closure (p. 325).** "The involutive closure of a distribution, denoted `Δ̄`, is
  the closure of `Δ` under bracketing; that is, `Δ̄` is the smallest distribution containing `Δ` such
  that if `f, g ∈ Δ̄` then `[f, g] ∈ Δ̄`": for smooth generators, the span over smooth functions of
  `L(g₁, …, g_m)` contains the generators, is closed under brackets, lies in every set of fields with
  these properties that is closed under sums and smooth multiples, and has the values of
  `L(g₁, …, g_m)` at each point (so its rank is the rank of `L(g₁, …, g_m)`, p. 326).
* **Level sets (pp. 318 and 340).** "For holonomic constraints the reachable set is some subset of
  the configuration space which lies in the level set `hᵢ(q) = hᵢ(q₀)`": a function whose derivative
  vanishes on the directions allowed by the constraints (on the input fields) is constant along every
  feasible curve (every trajectory of (7.10)), so the reachable set lies in its level set.
* **The integrating factor (7.4), p. 319.** "A single Pfaffian constraint is holonomic if and only
  if there exists an integrating factor `α(q)` such that `α(q)ω(q)` is the derivative of some function
  `h`", read pointwise with the kernel equality of Chapter 6 (`ker ω(q) = ker dh(q)`, `ω(q) ≠ 0`).
* **(7.5), p. 319.** `∂(αωⱼ)/∂qᵢ = ∂(αωᵢ)/∂qⱼ` when `αω = dh` near `q` with `h` of class `C²`
  (the symmetry of second derivatives), coordinate-free: `D(αω)(q) v v' = D(αω)(q) v' v`; and
  conversely ("the constraint is equivalent to `h(q) = 0` if there exists some integrating factor
  `α(q)` for which the equation (7.5) is true"), on an open convex set, through Mathlib's Poincaré
  lemma for closed one-forms: a nonvanishing `α` with `αω` differentiable and (7.5) gives `h` with
  `dh = αω` and `ker ω = ker dh` there.
* **(7.6), p. 320, and p. 328.** With `g₁(q), …, g_m(q)` spanning the null space of the constraints,
  `q(t)` is feasible exactly when `q̇ = g₁(q)u₁ + ⋯ + g_m(q)u_m` for some `u(t)`; the `u` is unique
  for independent `gⱼ(q)`.
* **The codistribution, p. 327, and `Δ = Ω^⊥`, p. 328.** `Ω_q = span{ω₁(q), …, ω_k(q)}` is the range
  of the transpose of `A(q)`; its annihilator is `Δ_q = ker A(q)`, `rank Ω_q + rank Δ_q = n`, `Ω`
  regular exactly when `Δ` is, and `rank Δ_q = n − k` for independent constraints.
* **Integrals of the constraints (pp. 339–341).** A function `h` of class `C^∞` on an open set with
  `L_{gⱼ} h = 0` for every input field has `L_f h = 0` for every `f ∈ L(g₁, …, g_m)`: its differential
  annihilates `Δ̄_q`. Hence "in the event that `Δ̄ = T_q ℝⁿ` … there are no nontrivial functions which
  integrate the given constraints", and `p` independent such functions satisfy
  `p + rank Δ̄_q ≤ n`, so `p ≤ k` (p. 339: "it follows that `p ≤ k`").
* **The degree of nonholonomy exists (p. 340).** "If a filtration is regular, then at each step of
  its construction, `Δᵢ` either gains dimension or `Δᵢ₊₁ = Δᵢ`, so that the construction terminates
  … there exists an integer `κ < n`": the smallest `κ ≥ 1` with `rank Δ_κ = rank Δ_{κ+1}` exists at
  every point, with `κ + rank Δ₁ ≤ n + 1`; so `κ < n` when `rank Δ₁ ≥ 2`.

**Conventions.** Constraints are `A : E → (E →L[ℝ] F)` (the rows `ωᵢ(q)` of the book's
`k × n` matrix are the components of `A(q)` in a basis of `F`), a single constraint is
`ω : E → (E →L[ℝ] ℝ)`; functions `h : E → ℝ` are the book's `hᵢ` one at a time; the derivative is
Mathlib's `fderiv`; trajectories are the library's `IsTrajectory` (continuous on `[0, T]`, the
equation away from finitely many times).

**Corrected printing.** p. 340 prints "there exists an integer `κ < n`". For one input on `ℝ`
(`n = 1`, `g₁ = 1`) the degree is `κ = 1 = n` (in the examples file); the bound that holds is
`κ ≤ n + 1 − rank Δ₁`, which gives `κ < n` whenever `rank Δ₁ ≥ 2`.

**Domain of the converse of (7.5).** The book works on `ℝⁿ`; the converse is proved on open convex
sets (the whole space included), the case Mathlib's Poincaré lemma covers.
-/

noncomputable section

open Set Filter Topology VectorField
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {m : ℕ}

/-! ### The involutive closure (p. 325) -/

/-- **MLS p. 325: the involutive closure `Δ̄` of `Δ = span{g₁, …, g_m}`,** the span over smooth
functions of the Lie algebra `L(g₁, …, g_m)` (a field `f` with `f = Σ cₖ wₖ`, `wₖ ∈ L(g)`, `cₖ`
smooth). -/
def InInvolutiveClosure (g : Fin m → E → E) (f : E → E) : Prop :=
  InSmoothSpan {k | InLieAlgebra g k} f

/-- **MLS p. 325: `Δ ⊆ Δ̄`:** the generators lie in the involutive closure. -/
theorem inInvolutiveClosure_gen (g : Fin m → E → E) (j : Fin m) :
    InInvolutiveClosure g (g j) :=
  InSmoothSpan.of_mem (InLieAlgebra.gen j)

/-- **MLS p. 325: "if `f, g ∈ Δ̄` then `[f, g] ∈ Δ̄`":** for smooth generators the involutive closure
is closed under the Lie bracket (through Proposition 7.1(3)). -/
theorem InInvolutiveClosure.bracket {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    {f h : E → E} (hf : InInvolutiveClosure g f) (hh : InInvolutiveClosure g h) :
    InInvolutiveClosure g (lieBracket ℝ f h) := by
  have hS : ∀ w ∈ {k | InLieAlgebra g k}, ContDiff ℝ ∞ w := fun w hw => InLieAlgebra.contDiff hg hw
  have hd : ∀ {k : E → E}, ContDiff ℝ ∞ k → Differentiable ℝ k :=
    fun hk => hk.differentiable (by simp)
  have hh' : ContDiff ℝ ∞ h := hh.contDiff hS
  -- `[w, h]` for `w ∈ L(g)`
  have hwh : ∀ w, InLieAlgebra g w → InInvolutiveClosure g (lieBracket ℝ w h) := by
    intro w hw
    have h1 := InSmoothSpan.lieBracket_left (hS w hw) hS hh
    refine InSmoothSpan.mono ?_ h1
    rintro k (hk | ⟨k', hk', rfl⟩)
    · exact hk
    · exact InLieAlgebra.bracket hw hk'
  induction hf with
  | zero =>
    rw [lieBracket_zero_left]
    exact InSmoothSpan.zero
  | @add_smul f w c hf hw hc ih =>
    have hf' : ContDiff ℝ ∞ f := hf.contDiff hS
    have hw' : ContDiff ℝ ∞ w := hS w hw
    have hdc : Differentiable ℝ c := hc.differentiable (by simp)
    have hLc : ContDiff ℝ ∞ (fun x => fderiv ℝ c x (h x)) :=
      (hc.fderiv_right (m := ∞) (by simp)).clm_apply hh'
    have key : lieBracket ℝ (fun x => f x + c x • w x) h =
        lieBracket ℝ f h + ((fun x => -(fderiv ℝ c x (h x)) • w x) +
          fun x => c x • lieBracket ℝ w h x) := by
      funext x
      have e : (fun x => f x + c x • w x) = f + fun x => c x • w x := rfl
      rw [e, lieBracket_add_left (V₁ := fun y => c y • w y) (hd hf' x)
          ((hdc x).smul (hd hw' x)), lieBracket_smul_left (hdc x) (hd hw' x)]
      simp
    rw [key]
    exact ih.add (((InSmoothSpan.of_mem hw).smul hLc.neg).add ((hwh w hw).smul hc))

/-- **MLS p. 325: `Δ̄` is the smallest such distribution:** every set `D` of fields that contains
the generators and `0` and is closed under sums, smooth multiples and brackets contains the
involutive closure. -/
theorem InInvolutiveClosure.mem_of_closed {g : Fin m → E → E} {D : Set (E → E)}
    (hgen : ∀ j, g j ∈ D) (hzero : (0 : E → E) ∈ D) (hadd : ∀ f ∈ D, ∀ h ∈ D, f + h ∈ D)
    (hsmul : ∀ c : E → ℝ, ContDiff ℝ ∞ c → ∀ f ∈ D, (fun x => c x • f x) ∈ D)
    (hbr : ∀ f ∈ D, ∀ h ∈ D, lieBracket ℝ f h ∈ D) {f : E → E} (hf : InInvolutiveClosure g f) :
    f ∈ D := by
  have hL : ∀ k, InLieAlgebra g k → k ∈ D := by
    intro k hk
    induction hk with
    | gen j => exact hgen j
    | add _ _ ihf ihh => exact hadd _ ihf _ ihh
    | smul c _ ih => exact hsmul (fun _ => c) contDiff_const _ ih
    | bracket _ _ ihf ihh => exact hbr _ ihf _ ihh
  induction hf with
  | zero => exact hzero
  | add_smul _ hw hc ih => exact hadd _ ih _ (hsmul _ hc _ (hL _ hw))

/-- **MLS pp. 325–326: `Δ̄_q` is `span{f(q) : f ∈ L(g₁, …, g_m)}`:** the values at `q` of the
involutive closure span the values of `L(g₁, …, g_m)` at `q`, so the rank of `Δ̄` is the rank of
`L(g₁, …, g_m)`. -/
theorem spanAt_involutiveClosure (g : Fin m → E → E) (q : E) :
    spanAt {f | InInvolutiveClosure g f} q = lieAlgebraAt g q := by
  apply le_antisymm
  · unfold spanAt
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact InSmoothSpan.mem_spanAt hf q
  · exact spanAt_mono (fun k hk => InSmoothSpan.of_mem hk) q

/-! ### Level sets of integrals of the constraints (pp. 318 and 340) -/

/-- **MLS p. 318: along a feasible curve, a function constant on the constraint directions is
constant.** If `x` is continuous on `[0, T]` and, away from finitely many times, has a derivative
`v` with `A(x(t)) v = 0`, and `h` is differentiable along `x` with `Dh(x(t)) v = 0` whenever
`A(x(t)) v = 0` (the kernel inclusion of an integrable constraint, Chapter 6), then
`h(x(T)) = h(x(0))`. -/
theorem apply_eq_of_pfaffian {A : E → E →L[ℝ] F} {h : E → ℝ} {x : ℝ → E} {T : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn x (Icc 0 T)) (S : Finset ℝ)
    (hx : ∀ t ∈ Ioo 0 T, t ∉ S → ∃ v, HasDerivAt x v t ∧ A (x t) v = 0)
    (hd : ∀ t ∈ Icc 0 T, DifferentiableAt ℝ h (x t))
    (hker : ∀ t ∈ Icc 0 T, ∀ v, A (x t) v = 0 → fderiv ℝ h (x t) v = 0) :
    h (x T) = h (x 0) := by
  have hhc : ContinuousOn (fun t => h (x t)) (Icc 0 T) := fun t ht =>
    (hd t ht).continuousAt.comp_continuousWithinAt (hc t ht)
  have H := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t => h (x t)) (fun _ => (0 : ℝ)) hT S.countable_toSet hhc (fun t ht => ?_)
    intervalIntegrable_const
  · simp only [intervalIntegral.integral_zero] at H
    linarith
  · obtain ⟨v, hv, hA⟩ := hx t ht.1 ht.2
    have hmem : t ∈ Icc 0 T := Ioo_subset_Icc_self ht.1
    have := (hd t hmem).hasFDerivAt.comp_hasDerivAt t hv
    rwa [hker t hmem v hA] at this

/-- **MLS pp. 318 and 340: a function whose derivative vanishes on the input fields is constant
along every trajectory of (7.10).** -/
theorem IsTrajectory.apply_eq_of_fderiv_eq_zero {g : Fin m → E → E} {u : ℝ → Fin m → ℝ} {T : ℝ}
    {x : ℝ → E} (hx : IsTrajectory g u T x) (hT : 0 ≤ T) {h : E → ℝ}
    (hd : ∀ t ∈ Icc 0 T, DifferentiableAt ℝ h (x t))
    (hL : ∀ t ∈ Icc 0 T, ∀ j, fderiv ℝ h (x t) (g j (x t)) = 0) :
    h (x T) = h (x 0) := by
  obtain ⟨hc, S, hS⟩ := hx
  refine apply_eq_of_pfaffian (A := fun q => fderiv ℝ h q) hT hc S
    (fun t ht hts => ⟨_, hS t ht hts, ?_⟩) hd (fun _ _ _ hv => hv)
  have hmem : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  simp only [driftFree, map_sum, map_smul, hL t hmem, smul_zero, Finset.sum_const_zero]

/-- **MLS p. 318: "for holonomic constraints the reachable set is some subset of the configuration
space which lies in the level set `hᵢ(q) = hᵢ(q₀)`":** if `h` is differentiable on `V` with
`L_{gⱼ} h = 0` there for every input field, then `R^V(q₀, T) ⊆ {q : h(q) = h(q₀)}` for `T ≥ 0`. -/
theorem reachableSet_subset_levelSet {g : Fin m → E → E} {U : Set (Fin m → ℝ)} {V : Set E}
    {q₀ : E} {T : ℝ} (hT : 0 ≤ T) {h : E → ℝ} (hd : ∀ q ∈ V, DifferentiableAt ℝ h q)
    (hL : ∀ q ∈ V, ∀ j, fderiv ℝ h q (g j q) = 0) :
    reachableSet g U V q₀ T ⊆ {q | h q = h q₀} := by
  rintro q ⟨u, x, -, hx, h0, hTq, hV⟩
  simp only [mem_ofPred_eq]
  rw [← hTq, ← h0]
  exact hx.apply_eq_of_fderiv_eq_zero hT (fun t ht => hd _ (hV t ht))
    (fun t ht j => hL _ (hV t ht) j)

/-! ### The integrating factor (7.4) and the condition (7.5), p. 319 -/

/-- **MLS (7.4), p. 319, pointwise: two linear forms with `ker ω ⊆ ker η` are proportional,**
`η = α ω` for some real `α`. -/
theorem ker_le_ker_iff_exists_smul {w η : E →L[ℝ] ℝ} :
    LinearMap.ker (w : E →ₗ[ℝ] ℝ) ≤ LinearMap.ker (η : E →ₗ[ℝ] ℝ) ↔ ∃ α : ℝ, η = α • w := by
  constructor
  · intro h
    have h' : ⨅ _ : Unit, LinearMap.ker (w : E →ₗ[ℝ] ℝ) ≤ LinearMap.ker (η : E →ₗ[ℝ] ℝ) := by
      simpa using h
    have hmem := mem_span_of_iInf_ker_le_ker h'
    rw [Set.range_const, Submodule.mem_span_singleton] at hmem
    obtain ⟨α, hα⟩ := hmem
    refine ⟨α, ?_⟩
    ext v
    have := congrArg (fun φ : E →ₗ[ℝ] ℝ => φ v) hα
    simpa using this.symm
  · rintro ⟨α, rfl⟩ v hv
    simp only [LinearMap.mem_ker] at hv ⊢
    simp [hv]

/-- **MLS (7.4), p. 319: "a single Pfaffian constraint is holonomic if and only if there exists an
integrating factor `α(q)` such that `α(q)ω(q)` is the derivative of some function `h`",** on a set
`Q`, with the library's kernel-equality notion of integrability (Chapter 6, pp. 267–268) and a
nonvanishing constraint (the independence of (7.2)): `ker ω(q) = ker Dh(q)` with `ω(q) ≠ 0` at
every `q ∈ Q` exactly when `Dh(q) = α(q) ω(q)` with `α(q) ≠ 0` and `ω(q) ≠ 0` there. -/
theorem integratingFactor_iff {w : E → E →L[ℝ] ℝ} {h : E → ℝ} {Q : Set E} :
    (∀ q ∈ Q, w q ≠ 0 ∧
        LinearMap.ker (w q : E →ₗ[ℝ] ℝ) = LinearMap.ker (fderiv ℝ h q : E →ₗ[ℝ] ℝ)) ↔
      ∃ α : E → ℝ, ∀ q ∈ Q, α q ≠ 0 ∧ w q ≠ 0 ∧ fderiv ℝ h q = α q • w q := by
  constructor
  · intro H
    choose! α hα using fun q hq => ker_le_ker_iff_exists_smul.1 (H q hq).2.le
    refine ⟨α, fun q hq => ⟨?_, (H q hq).1, hα q hq⟩⟩
    intro h0
    have hk := (H q hq).2
    rw [hα q hq, h0, zero_smul] at hk
    have hne := (H q hq).1
    apply hne
    ext v
    have : v ∈ LinearMap.ker (w q : E →ₗ[ℝ] ℝ) := by rw [hk]; simp
    simpa using this
  · rintro ⟨α, hα⟩ q hq
    obtain ⟨ha, hω, hd⟩ := hα q hq
    refine ⟨hω, ?_⟩
    rw [hd]
    ext v
    simp [ha]

/-- **MLS (7.5), p. 319: `∂(αωⱼ)/∂qᵢ = ∂(αωᵢ)/∂qⱼ`.** If `α(y)ω(y) = Dh(y)` near `q` and `h` is
of class `C²` at `q`, the derivative of `y ↦ α(y)ω(y)` at `q` is symmetric:
`D(αω)(q) v v' = D(αω)(q) v' v` (with `v = eᵢ`, `v' = eⱼ` on `ℝⁿ` this is (7.5)); the
one-form `ω` is the argument `w`. -/
theorem integratingFactor_symm {w : E → E →L[ℝ] ℝ} {α : E → ℝ} {h : E → ℝ} {q : E}
    (hh : ContDiffAt ℝ 2 h q) (heq : ∀ᶠ y in 𝓝 q, fderiv ℝ h y = α y • w y) (v v' : E) :
    fderiv ℝ (fun y => α y • w y) q v v' = fderiv ℝ (fun y => α y • w y) q v' v := by
  have hfd : fderiv ℝ (fun y => α y • w y) q = fderiv ℝ (fderiv ℝ h) q :=
    (Filter.EventuallyEq.fderiv_eq (heq.mono fun y hy => hy.symm))
  rw [hfd]
  exact hh.isSymmSndFDerivAt (by simp) v v'

/-- **MLS (7.5), p. 319, converse: "the constraint is equivalent to `h(q) = 0` if there exists some
integrating factor `α(q)` for which the equation (7.5) is true".** On an open convex set `s` (the
whole space included), if `y ↦ α(y)ω(y)` is differentiable on `s` with symmetric derivative ((7.5))
and `α(y) ≠ 0`, `ω(y) ≠ 0` on `s`, there is `h` with `Dh(y) = α(y)ω(y)` and
`ker ω(y) = ker Dh(y)` at every `y ∈ s` (Mathlib's Poincaré lemma for closed one-forms on convex
sets). -/
theorem exists_integral_of_integratingFactor_symm {w : E → E →L[ℝ] ℝ} {α : E → ℝ} {s : Set E}
    (hs : Convex ℝ s) (hso : IsOpen s) (hd : DifferentiableOn ℝ (fun y => α y • w y) s)
    (hsymm : ∀ y ∈ s, ∀ v v', fderiv ℝ (fun y => α y • w y) y v v' =
      fderiv ℝ (fun y => α y • w y) y v' v)
    (hα : ∀ y ∈ s, α y ≠ 0) (hw : ∀ y ∈ s, w y ≠ 0) :
    ∃ h : E → ℝ, ∀ y ∈ s, HasFDerivAt h (α y • w y) y ∧
      LinearMap.ker (w y : E →ₗ[ℝ] ℝ) = LinearMap.ker (fderiv ℝ h y : E →ₗ[ℝ] ℝ) := by
  obtain ⟨h, hh⟩ := hs.exists_forall_hasFDerivAt_of_fderiv_symmetric hso hd hsymm
  refine ⟨h, fun y hy => ⟨hh y hy, ?_⟩⟩
  have hI := (integratingFactor_iff (w := w) (h := h) (Q := s)).2
    ⟨α, fun y hy => ⟨hα y hy, hw y hy, (hh y hy).fderiv⟩⟩
  exact (hI y hy).2

/-! ### The control form (7.6), p. 320, and p. 328 -/

/-- **MLS (7.6), p. 320: with `g₁(q), …, g_m(q)` a basis (or a spanning set) of the null space of
the constraints, a velocity `v` satisfies `A(q) v = 0` exactly when `v = Σⱼ uⱼ gⱼ(q)` for some
`u ∈ ℝ^m`.** -/
theorem apply_eq_zero_iff_exists_driftFree {A : E → E →L[ℝ] F} {g : Fin m → E → E} {q : E}
    (hspan : Submodule.span ℝ (Set.range fun j => g j q) = LinearMap.ker (A q : E →ₗ[ℝ] F)) (v : E) :
    A q v = 0 ↔ ∃ u : Fin m → ℝ, v = driftFree g q u := by
  have : v ∈ LinearMap.ker (A q : E →ₗ[ℝ] F) ↔ v ∈ Submodule.span ℝ (Set.range fun j => g j q) := by
    rw [hspan]
  rw [LinearMap.mem_ker, Submodule.mem_span_range_iff_exists_fun] at this
  change (A q : E →ₗ[ℝ] F) v = 0 ↔ _
  rw [this]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [← hc]; rfl⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc]; rfl⟩

/-- **MLS p. 320: the input of (7.6) is unique** when `g₁(q), …, g_m(q)` are linearly
independent. -/
theorem driftFree_injective {g : Fin m → E → E} {q : E}
    (hli : LinearIndependent ℝ fun j => g j q) : Function.Injective (driftFree g q) := by
  intro u w h
  have h' : ∑ j, (u - w) j • g j q = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 h
  funext j
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli (u - w) h' j)

/-- **MLS (7.6), p. 320: "`q(t)` is a feasible trajectory for the system if and only if `q(t)`
satisfies equation (7.6) for some choice of controls `u(t) ∈ ℝ^m`":** for a curve with velocity
`x'` on a set of times `I`, with `g₁, …, g_m` spanning the null space of the constraints along the
curve, `A(x(t)) x'(t) = 0` for all `t ∈ I` exactly when `x'(t) = Σⱼ uⱼ(t) gⱼ(x(t))` for some
`u : ℝ → ℝ^m`. -/
theorem feasible_iff_exists_input {A : E → E →L[ℝ] F} {g : Fin m → E → E} {x x' : ℝ → E}
    {I : Set ℝ}
    (hspan : ∀ t ∈ I, Submodule.span ℝ (Set.range fun j => g j (x t)) = LinearMap.ker (A (x t) : E →ₗ[ℝ] F)) :
    (∀ t ∈ I, A (x t) (x' t) = 0) ↔
      ∃ u : ℝ → Fin m → ℝ, ∀ t ∈ I, x' t = driftFree g (x t) (u t) := by
  constructor
  · intro h
    choose! u hu using fun t ht => (apply_eq_zero_iff_exists_driftFree (hspan t ht) (x' t)).1 (h t ht)
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩ t ht
    exact (apply_eq_zero_iff_exists_driftFree (hspan t ht) (x' t)).2 ⟨u t, hu t ht⟩

/-! ### The codistribution and `Δ = Ω^⊥` (pp. 327–328) -/

/-- **MLS p. 327: the codistribution `Ω_q = span{ω₁(q), …, ω_k(q)}`** of the constraints
`A(q) q̇ = 0`, the range of the transpose of `A(q)` (the linear forms `φ ∘ A(q)`). -/
def codistributionAt (A : E → E →L[ℝ] F) (q : E) : Submodule ℝ (Module.Dual ℝ E) :=
  LinearMap.range ((A q : E →ₗ[ℝ] F).dualMap)

/-- **MLS p. 327:** the rows `φ ∘ A(q)` of the constraints lie in `Ω_q`. -/
theorem comp_mem_codistributionAt (A : E → E →L[ℝ] F) (q : E) (φ : Module.Dual ℝ F) :
    φ ∘ₗ (A q : E →ₗ[ℝ] F) ∈ codistributionAt A q :=
  ⟨φ, rfl⟩

/-- **MLS p. 328: `Δ = Ω^⊥`:** the vectors annihilated by every form of the codistribution are the
null space `ker A(q)` (finite dimension). -/
theorem dualCoannihilator_codistributionAt [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (A : E → E →L[ℝ] F) (q : E) :
    (codistributionAt A q).dualCoannihilator = LinearMap.ker (A q : E →ₗ[ℝ] F) := by
  rw [codistributionAt, LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    Subspace.dualAnnihilator_dualCoannihilator_eq]

/-- **MLS pp. 327–328: `rank Ω_q + rank Δ_q = n`** (finite dimension). -/
theorem finrank_codistributionAt_add [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (A : E → E →L[ℝ] F) (q : E) :
    Module.finrank ℝ (codistributionAt A q) + Module.finrank ℝ (LinearMap.ker (A q : E →ₗ[ℝ] F)) =
      Module.finrank ℝ E := by
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq (codistributionAt A q)
  rw [dualCoannihilator_codistributionAt] at h
  exact h

/-- **MLS pp. 327–328 (Proposition 7.3's count `n − k`):** for `k` independent constraints
(`A(q)` onto a `k`-dimensional `F`), `rank Ω_q = k` and `rank Δ_q = n − k`. -/
theorem finrank_ker_of_surjective [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {A : E → E →L[ℝ] F} {q : E} (hA : Function.Surjective (A q)) :
    Module.finrank ℝ (codistributionAt A q) = Module.finrank ℝ F ∧
      Module.finrank ℝ (LinearMap.ker (A q : E →ₗ[ℝ] F)) = Module.finrank ℝ E - Module.finrank ℝ F := by
  have hr : Module.finrank ℝ (codistributionAt A q) = Module.finrank ℝ F := by
    rw [codistributionAt, LinearMap.finrank_range_dualMap_eq_finrank_range,
      LinearMap.range_eq_top.2 hA, finrank_top]
  have h := finrank_codistributionAt_add A q
  omega

/-- **MLS p. 327: "the codistribution `Ω` is said to be regular if its rank is constant";** on a
set `U` it is regular exactly when the annihilating distribution `Δ = ker A` is (finite
dimension). -/
theorem isRegularOn_ker_iff [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (A : E → E →L[ℝ] F) (U : Set E) :
    (∃ r : ℕ, ∀ q ∈ U, Module.finrank ℝ (codistributionAt A q) = r) ↔
      IsRegularOn (fun q => LinearMap.ker (A q : E →ₗ[ℝ] F)) U := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨Module.finrank ℝ E - r, fun q hq => ?_⟩
    have h := finrank_codistributionAt_add A q
    have := hr q hq
    simp only
    omega
  · rintro ⟨r, hr⟩
    refine ⟨Module.finrank ℝ E - r, fun q hq => ?_⟩
    have h := finrank_codistributionAt_add A q
    have := hr q hq
    simp only at this
    omega

/-! ### Integrals of the constraints annihilate the controllability Lie algebra (pp. 339–341) -/

/-- **MLS pp. 339–341: an integral of the constraints is annihilated by `L(g₁, …, g_m)`.** For
smooth input fields and `h` of class `C^∞` on an open set `U` with `L_{gⱼ} h = 0` on `U` for every
`j`, every `f ∈ L(g₁, …, g_m)` has `L_f h = 0` on `U` (through `L_{[f,k]} = L_f L_k − L_k L_f`,
p. 325). -/
theorem fderiv_apply_eq_zero_of_inLieAlgebra {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    {U : Set E} (hU : IsOpen U) {h : E → ℝ} (hh : ContDiffOn ℝ ∞ h U)
    (h0 : ∀ y ∈ U, ∀ j, fderiv ℝ h y (g j y) = 0) {f : E → E} (hf : InLieAlgebra g f) :
    ∀ y ∈ U, fderiv ℝ h y (f y) = 0 := by
  induction hf with
  | gen j => exact fun y hy => h0 y hy j
  | add _ _ ihf ihk => intro y hy; simp [ihf y hy, ihk y hy]
  | smul c _ ih => intro y hy; simp [ih y hy]
  | @bracket f k hf hk ihf ihk =>
    intro y hy
    have hh2 : ContDiffAt ℝ 2 h y := (hh.contDiffAt (hU.mem_nhds hy)).of_le (by simp)
    have hfd := (hf.contDiff hg).differentiable (by simp) y
    have hkd := (hk.contDiff hg).differentiable (by simp) y
    have key := lieDerivative_lieBracket (α := h) hh2 hfd hkd
    have e1 : lieDerivative k h =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (hU.mem_nhds hy) fun q hq => ihk q hq
    have e2 : lieDerivative f h =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (hU.mem_nhds hy) fun q hq => ihf q hq
    change lieDerivative (lieBracket ℝ f k) h y = 0
    rw [key, lieDerivative_apply, lieDerivative_apply, e1.fderiv_eq, e2.fderiv_eq]
    simp

/-- **MLS pp. 339–341: the differential of an integral of the constraints annihilates `Δ̄_q`,**
the values at `q` of `L(g₁, …, g_m)`. -/
theorem fderiv_apply_eq_zero_of_mem_lieAlgebraAt {g : Fin m → E → E}
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) {U : Set E} (hU : IsOpen U) {h : E → ℝ}
    (hh : ContDiffOn ℝ ∞ h U) (h0 : ∀ y ∈ U, ∀ j, fderiv ℝ h y (g j y) = 0) {y : E} (hy : y ∈ U)
    {v : E} (hv : v ∈ lieAlgebraAt g y) : fderiv ℝ h y v = 0 := by
  have hle : lieAlgebraAt g y ≤ LinearMap.ker (fderiv ℝ h y : E →ₗ[ℝ] ℝ) := by
    unfold lieAlgebraAt spanAt
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact fderiv_apply_eq_zero_of_inLieAlgebra hg hU hh h0 hf y hy
  exact hle hv

/-- **MLS p. 339: "in the event that `Δ̄ = T_q ℝⁿ` for all `q`, then `p = 0`, i.e., there are no
nontrivial functions which integrate the given constraints":** where the controllability Lie
algebra has full rank, an integral of the constraints has zero differential. -/
theorem fderiv_eq_zero_of_lieAlgebraAt_eq_top {g : Fin m → E → E}
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) {U : Set E} (hU : IsOpen U) {h : E → ℝ}
    (hh : ContDiffOn ℝ ∞ h U) (h0 : ∀ y ∈ U, ∀ j, fderiv ℝ h y (g j y) = 0) {y : E} (hy : y ∈ U)
    (htop : lieAlgebraAt g y = ⊤) : fderiv ℝ h y = 0 := by
  ext v
  exact fderiv_apply_eq_zero_of_mem_lieAlgebraAt hg hU hh h0 hy (htop ▸ Submodule.mem_top)

/-- **MLS pp. 339–341: the number of independent integrals of the constraints:** `p` functions
`h₁, …, h_p` as above with linearly independent differentials at `y` satisfy
`p + rank Δ̄_y ≤ n` (p. 341: their differentials span at most `(Δ̄)^⊥`). -/
theorem card_add_finrank_lieAlgebraAt_le [FiniteDimensional ℝ E] {g : Fin m → E → E}
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) {U : Set E} (hU : IsOpen U) {p : ℕ} {h : Fin p → E → ℝ}
    (hh : ∀ i, ContDiffOn ℝ ∞ (h i) U) (h0 : ∀ i, ∀ y ∈ U, ∀ j, fderiv ℝ (h i) y (g j y) = 0)
    {y : E} (hy : y ∈ U)
    (hli : LinearIndependent ℝ fun i => (fderiv ℝ (h i) y : Module.Dual ℝ E)) :
    p + Module.finrank ℝ (lieAlgebraAt g y) ≤ Module.finrank ℝ E := by
  have hsub : Submodule.span ℝ (Set.range fun i => (fderiv ℝ (h i) y : Module.Dual ℝ E)) ≤
      (lieAlgebraAt g y).dualAnnihilator := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
    intro v hv
    exact fderiv_apply_eq_zero_of_mem_lieAlgebraAt hg hU (hh i) (h0 i) hy hv
  have h1 := Submodule.finrank_mono hsub
  rw [finrank_span_eq_card hli, Fintype.card_fin] at h1
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq (lieAlgebraAt g y)
  have h3 := Nat.add_le_add_left h1 (Module.finrank ℝ (lieAlgebraAt g y))
  rw [add_comm]
  exact h3.trans h2.le

/-- **MLS p. 339: "since the dimension of `Δ̄` is greater than or equal to the dimension of `Δ`, it
follows that `p ≤ k`":** with the bound above, `p + rank Δ_y ≤ n`; for `Δ_y = ker A(y)` of rank
`n − k` this is `p ≤ k`. -/
theorem card_add_finrank_spanAt_le [FiniteDimensional ℝ E] {g : Fin m → E → E}
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) {U : Set E} (hU : IsOpen U) {p : ℕ} {h : Fin p → E → ℝ}
    (hh : ∀ i, ContDiffOn ℝ ∞ (h i) U) (h0 : ∀ i, ∀ y ∈ U, ∀ j, fderiv ℝ (h i) y (g j y) = 0)
    {y : E} (hy : y ∈ U)
    (hli : LinearIndependent ℝ fun i => (fderiv ℝ (h i) y : Module.Dual ℝ E)) :
    p + Module.finrank ℝ (spanAt (Set.range g) y) ≤ Module.finrank ℝ E := by
  have h1 := card_add_finrank_lieAlgebraAt_le hg hU hh h0 hy hli
  have h2 : Module.finrank ℝ (spanAt (Set.range g) y) ≤ Module.finrank ℝ (lieAlgebraAt g y) := by
    apply Submodule.finrank_mono
    rw [← filtrationAt_one]
    exact filtrationAt_le_lieAlgebraAt g 1 y
  omega

/-! ### The degree of nonholonomy exists (p. 340) -/

/-- **MLS p. 340 and Definition 7.2: the construction of the filtration terminates:** at every
point of a finite-dimensional space the degree of nonholonomy `κ` exists, with
`κ + rank Δ₁ ≤ n + 1` (the rank gains at least one at every step before `κ`). -/
theorem exists_isDegreeOfNonholonomy [FiniteDimensional ℝ E] (g : Fin m → E → E) (q : E) :
    ∃ κ, IsDegreeOfNonholonomy g q κ ∧ κ + growth g 1 q ≤ Module.finrank ℝ E + 1 := by
  set n := Module.finrank ℝ E
  have hstep : ∀ k, (∀ i, 1 ≤ i → i ≤ k → growth g i q < growth g (i + 1) q) →
      growth g 1 q + k ≤ growth g (k + 1) q := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro H
      have h1 := ih fun i hi hik => H i hi (by omega)
      have h2 := H (k + 1) (by omega) le_rfl
      omega
  have hex : ∃ i, 1 ≤ i ∧ growth g i q = growth g (i + 1) q := by
    by_contra hne
    push Not at hne
    have H : ∀ i, 1 ≤ i → i ≤ n + 1 → growth g i q < growth g (i + 1) q := fun i hi _ =>
      lt_of_le_of_ne (growth_mono g (Nat.le_succ i) q) (hne i hi)
    have h1 := hstep (n + 1) H
    have h2 := growth_le_finrank g (n + 1 + 1) q
    omega
  classical
  let κ := Nat.find hex
  have hκ : 1 ≤ κ ∧ growth g κ q = growth g (κ + 1) q := Nat.find_spec hex
  have hlt : ∀ i, 1 ≤ i → i < κ → growth g i q < growth g (i + 1) q := by
    intro i hi hik
    have hni := Nat.find_min hex hik
    push Not at hni
    exact lt_of_le_of_ne (growth_mono g (Nat.le_succ i) q) (hni hi)
  refine ⟨κ, ⟨hκ.1, hκ.2, hlt⟩, ?_⟩
  have h1 := hstep (κ - 1) fun i hi hik => hlt i hi (by omega)
  have h2 := growth_le_finrank g (κ - 1 + 1) q
  omega

/-- **MLS p. 340: "there exists an integer `κ < n`",** under the hypothesis `rank Δ₁ ≥ 2` (two
independent input fields at `q`), which the printed claim needs (see the corrected printing in the
module header). -/
theorem isDegreeOfNonholonomy_lt_finrank [FiniteDimensional ℝ E] {g : Fin m → E → E} {q : E}
    (h2 : 2 ≤ growth g 1 q) : ∃ κ, IsDegreeOfNonholonomy g q κ ∧ κ < Module.finrank ℝ E := by
  obtain ⟨κ, hκ, hb⟩ := exists_isDegreeOfNonholonomy g q
  exact ⟨κ, hκ, by omega⟩

end Nonholonomic
end RoboLean
