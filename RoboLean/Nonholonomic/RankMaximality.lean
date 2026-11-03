import RoboLean.Nonholonomic.ChowJacobi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The maximal-rank step of Chow's theorem (MLS Propositions 7.6–7.7, pp. 330–331)

**What MLS prints.** Proposition 7.6 (p. 330): "If `Δ_q = T_q ℝⁿ` for all `q` in some neighborhood
of `q₀`, then for any `T > 0` and neighborhood `V` of `q₀`, `int R^V(q₀, ≤ T)` is non-empty." The
proof builds manifolds `N_k = {φ^{f_k}_{t_k} ∘ ⋯ ∘ φ^{f₁}_{t₁}(q₀) : 0 < tᵢ < εᵢ}` and, while
`k < n`, finds `q ∈ N_k` and `f_{k+1} ∈ Δ` with `f_{k+1}(q) ∉ T_q N_k`, since otherwise
`Δ|_W ⊂ T N_k` on an open `W ⊂ N_k`. Proposition 7.7 (p. 331) maps a neighbourhood of the end
point `q_f` back to a neighbourhood of `q₀` by the reversed input, "`(φ^u_{T/2})^{−1}(W)` is a
neighborhood of `q₀`".

**Source observation.** The printed `N_{k+1}` composes flows of fields `f_{k+1} ∈ Δ`; a flow of a
bracket is not a flow of (7.10), so those points need not be reachable. The argument below (the
maximal-rank argument of Krener and Sussmann) composes flows of the generators only: if every
generator is tangent at the points of maximal rank, so is every left-normed bracket, because the
bracket `[gⱼ, Z](y)` is the derivative at `σ = 0` of `(Dφ^{gⱼ}_σ(y))⁻¹ Z(φ^{gⱼ}_σ(y))`.

**Proved here.** For maps `Φⱼ : ℝ → E → E` with the properties of the two-sided flows of fields
`Xⱼ` (`IsFlowFamily`: jointly `C¹`, `Φⱼ(0) = id`, `Φⱼ(−t) ∘ Φⱼ(t) = id`, `t ↦ Φⱼ(t, x)` an integral
curve of `Xⱼ`, and the right derivative of `D_xΦⱼ(σ, y)` at `σ = 0` equal to `DXⱼ(y)`), the
composition `flowSeq Φ x r w s = Φ_{w_{r−1}}(s_{r−1}) ∘ ⋯ ∘ Φ_{w₀}(s₀)(x)`:

* is `C¹` in the times and the initial point (`contDiff_flowSeq`), moves `x` by at most
  `M Σ |sᵢ|` when `‖Xⱼ‖ ≤ M` (`norm_flowSeq_sub_le`), and is undone by the reversed word with
  negated times (`exists_flowSeq_undo`);
* the maximal-rank step (`exists_range_fderiv_flowSeq_eq_top`): on a finite-dimensional space,
  for smooth `Xⱼ`, if the left-normed brackets of the `Xⱼ` span `E` at every point
  `flowSeq Φ q r w s` with `Σ |sᵢ| < δ`, then some word `w` and times `s` with `Σ |sᵢ| < δ` give a
  surjective derivative of `s ↦ flowSeq Φ q r w s`;
* the reversal step of Proposition 7.7 (`map_nhds_flowSeq_undo`): composing with the undoing word,
  `s′ ↦ flowSeq Φ (flowSeq Φ q r w s′) r w′ s″` maps every neighbourhood of `s` onto a
  neighbourhood of `q`, by the inverse function theorem.

**Conventions.** Time first; `flowSeq` applies the letter at index `0` first and the last letter
last (`flowSeq_snoc`, `flowSeq_cons`); times `s : Fin r → ℝ` may have either sign (the inputs are
unconstrained, so `±eⱼ` are both admissible); `Σ |sᵢ|` is the total time spent. Derivatives are
Fréchet derivatives; ranges of derivatives are `LinearMap.range`; brackets are Mathlib's
`lieBracket` (the book's sign).
-/

noncomputable section

open Set Filter Topology VectorField
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- **MLS pp. 322–323, the properties of the flows `φ^{Xⱼ}_t` used by Propositions 7.6–7.7
(pp. 330–331):** `(t, x) ↦ Φⱼ(t, x)` is `C¹`, `Φⱼ(0, x) = x`, `Φⱼ(−t, Φⱼ(t, x)) = x`,
`t ↦ Φⱼ(t, x)` has derivative `Xⱼ(Φⱼ(t, x))`, and `σ ↦ D_xΦⱼ(σ, y)` has the right derivative
`DXⱼ(y)` at `σ = 0` (the variational equation at time `0`). The two-sided flows of the library
have these properties (`Nonholonomic/Chow`). -/
structure IsFlowFamily (X : Fin m → E → E) (Φ : Fin m → ℝ → E → E) : Prop where
  /-- `(t, x) ↦ Φⱼ(t, x)` is `C¹`. -/
  contDiff : ∀ j, ContDiff ℝ 1 fun p : ℝ × E => Φ j p.1 p.2
  /-- `Φⱼ(0) = id`. -/
  zero : ∀ j x, Φ j 0 x = x
  /-- `Φⱼ(−t) ∘ Φⱼ(t) = id`. -/
  neg_comp : ∀ j t x, Φ j (-t) (Φ j t x) = x
  /-- `t ↦ Φⱼ(t, x)` is an integral curve of `Xⱼ`. -/
  hasDerivAt : ∀ j t x, HasDerivAt (fun s => Φ j s x) (X j (Φ j t x)) t
  /-- The right derivative of `σ ↦ D_xΦⱼ(σ, y)` at `0` is `DXⱼ(y)`. -/
  hasDerivWithinAt_fderiv : ∀ j y,
    HasDerivWithinAt (fun s => fderiv ℝ (Φ j s) y) (fderiv ℝ (X j) y) (Ici 0) 0

/-- **MLS p. 330 (the points of `N_k`) and p. 331 (the flow `φ^u_t` of a piecewise constant
input): the composed flow** `Φ_{w_{r−1}}(s_{r−1}) ∘ ⋯ ∘ Φ_{w₀}(s₀)(x)`, the letter at index `0`
applied first. -/
def flowSeq (Φ : Fin m → ℝ → E → E) (x : E) : (r : ℕ) → (Fin r → Fin m) → (Fin r → ℝ) → E
  | 0, _, _ => x
  | r + 1, w, s => Φ (w (Fin.last r)) (s (Fin.last r)) (flowSeq Φ x r (Fin.init w) (Fin.init s))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **MLS p. 330: one more factor `φ^{f_{k+1}}_{t_{k+1}}` applied last.** -/
theorem flowSeq_snoc (Φ : Fin m → ℝ → E → E) (x : E) {r : ℕ} (w : Fin r → Fin m)
    (s : Fin r → ℝ) (j : Fin m) (σ : ℝ) :
    flowSeq Φ x (r + 1) (Fin.snoc w j) (Fin.snoc s σ) = Φ j σ (flowSeq Φ x r w s) := by
  simp [flowSeq, Fin.init_snoc, Fin.snoc_last]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **MLS p. 330: one more factor applied first.** -/
theorem flowSeq_cons (Φ : Fin m → ℝ → E → E) (x : E) {r : ℕ} (w : Fin r → Fin m)
    (s : Fin r → ℝ) (j : Fin m) (σ : ℝ) :
    flowSeq Φ x (r + 1) (Fin.cons j w) (Fin.cons σ s) = flowSeq Φ (Φ j σ x) r w s := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [← Fin.snoc_init_self w, ← Fin.snoc_init_self s, Fin.cons_snoc_eq_snoc_cons,
      Fin.cons_snoc_eq_snoc_cons, flowSeq_snoc, flowSeq_snoc, ih]

/-- **MLS pp. 330–331: the composed flow is `C¹` in the times and the initial point** when every
`(t, x) ↦ Φⱼ(t, x)` is. -/
theorem contDiff_flowSeq {Φ : Fin m → ℝ → E → E}
    (hΦ : ∀ j, ContDiff ℝ 1 fun p : ℝ × E => Φ j p.1 p.2) (r : ℕ) (w : Fin r → Fin m) :
    ContDiff ℝ 1 fun p : (Fin r → ℝ) × E => flowSeq Φ p.2 r w p.1 := by
  induction r with
  | zero => exact contDiff_snd
  | succ r ih =>
    have hinit : ContDiff ℝ 1 fun p : (Fin (r + 1) → ℝ) × E => Fin.init p.1 :=
      contDiff_pi.2 fun i => (contDiff_apply ℝ ℝ _).comp contDiff_fst
    exact (hΦ (w (Fin.last r))).comp (((contDiff_apply ℝ ℝ (Fin.last r)).comp contDiff_fst).prodMk
      ((ih (Fin.init w)).comp (hinit.prodMk contDiff_snd)))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **MLS p. 331 (Proposition 7.7, "we can flow backwards from `q_f` to `q₀`"): the composed flow
is undone by the reversed word with negated times,** of the same total time `Σ |sᵢ|`. -/
theorem exists_flowSeq_undo {Φ : Fin m → ℝ → E → E} (hneg : ∀ j t x, Φ j (-t) (Φ j t x) = x)
    (r : ℕ) (w : Fin r → Fin m) (s : Fin r → ℝ) :
    ∃ (w' : Fin r → Fin m) (s' : Fin r → ℝ), ∑ i, |s' i| = ∑ i, |s i| ∧
      ∀ x, flowSeq Φ (flowSeq Φ x r w s) r w' s' = x := by
  induction r with
  | zero => exact ⟨w, s, rfl, fun x => rfl⟩
  | succ r ih =>
    obtain ⟨w₀, s₀, h₁, h₂⟩ := ih (Fin.init w) (Fin.init s)
    refine ⟨Fin.cons (w (Fin.last r)) w₀, Fin.cons (-(s (Fin.last r))) s₀, ?_, fun x => ?_⟩
    · rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
      simp only [Fin.cons_zero, Fin.cons_succ, abs_neg, h₁, Fin.init]
      ring
    · rw [flowSeq_cons]
      show flowSeq Φ (Φ _ (-_) (Φ (w (Fin.last r)) (s (Fin.last r))
        (flowSeq Φ x r (Fin.init w) (Fin.init s)))) r w₀ s₀ = x
      rw [hneg, h₂]

/-- **MLS p. 330 ("take `N₁ ⊂ V`", "we can assume `N_{k+1} ⊂ V`"): the composed flow stays within
`M Σ |sᵢ|` of its initial point** when every `Xⱼ` is bounded by `M` and `t ↦ Φⱼ(t, x)` is an
integral curve of `Xⱼ`. -/
theorem norm_flowSeq_sub_le {X : Fin m → E → E} {Φ : Fin m → ℝ → E → E} {M : ℝ}
    (hM : ∀ j y, ‖X j y‖ ≤ M)
    (hd : ∀ j t x, HasDerivAt (fun s => Φ j s x) (X j (Φ j t x)) t) (hz : ∀ j x, Φ j 0 x = x)
    (x : E) (r : ℕ) (w : Fin r → Fin m) (s : Fin r → ℝ) :
    ‖flowSeq Φ x r w s - x‖ ≤ M * ∑ i, |s i| := by
  have hseg : ∀ j t y, ‖Φ j t y - y‖ ≤ M * |t| := by
    intro j t y
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun τ => Φ j τ y)
      (f' := fun τ => X j (Φ j τ y)) (s := univ) (x := 0) (y := t)
      (fun τ _ => (hd j τ y).hasDerivWithinAt) (fun τ _ => hM j _) convex_univ (mem_univ _)
      (mem_univ _)
    simpa [hz, Real.norm_eq_abs] using h
  induction r with
  | zero => simp [flowSeq]
  | succ r ih =>
    show ‖Φ (w (Fin.last r)) (s (Fin.last r)) (flowSeq Φ x r (Fin.init w) (Fin.init s)) - x‖ ≤ _
    have h1 := hseg (w (Fin.last r)) (s (Fin.last r)) (flowSeq Φ x r (Fin.init w) (Fin.init s))
    have h2 := ih (Fin.init w) (Fin.init s)
    rw [Fin.sum_univ_castSucc]
    calc _ ≤ ‖Φ (w (Fin.last r)) (s (Fin.last r)) (flowSeq Φ x r (Fin.init w) (Fin.init s)) -
          flowSeq Φ x r (Fin.init w) (Fin.init s)‖ +
          ‖flowSeq Φ x r (Fin.init w) (Fin.init s) - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ M * |s (Fin.last r)| + M * ∑ i, |Fin.init s i| := add_le_add h1 h2
      _ = _ := by simp only [Fin.init]; ring

/-- **MLS Proposition 7.6, p. 330, the maximal-rank step (with only the generators' flows; see the
source observation in the module docstring):** on a finite-dimensional space, let `Φ` have the
flow properties of `IsFlowFamily` for smooth fields `X`, and let the left-normed brackets of the
`Xⱼ` span `E` at every point `flowSeq Φ q r w s` with `Σ |sᵢ| < δ`, `δ > 0`. Then for some word
`w` of length `r` and times `s` with `Σ |sᵢ| < δ`, the derivative of `s ↦ flowSeq Φ q r w s` at
`s` is onto `E`. -/
theorem exists_range_fderiv_flowSeq_eq_top [FiniteDimensional ℝ E] {X : Fin m → E → E}
    {Φ : Fin m → ℝ → E → E} (hΦ : IsFlowFamily X Φ) (hX : ∀ j, ContDiff ℝ ∞ (X j)) {q : E}
    {δ : ℝ} (hδ : 0 < δ) {W : Set E}
    (hW : ∀ r (w : Fin r → Fin m) (s : Fin r → ℝ), ∑ i, |s i| < δ → flowSeq Φ q r w s ∈ W)
    (hspan : ∀ p ∈ W, spanAt (leftNormedFields X) p = ⊤) :
    ∃ r, ∃ w : Fin r → Fin m, ∃ s : Fin r → ℝ, ∑ i, |s i| < δ ∧
      (fderiv ℝ (flowSeq Φ q r w) s).range = ⊤ := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hΦs : ∀ j t, ContDiff ℝ 1 (Φ j t) := fun j t =>
    (hΦ.contDiff j).comp (contDiff_const.prodMk contDiff_id)
  have hdS : ∀ j t x, DifferentiableAt ℝ (Φ j t) x := fun j t x =>
    (hΦs j t).differentiable one_ne_zero x
  have hdT : ∀ r (w : Fin r → Fin m) (s : Fin r → ℝ), DifferentiableAt ℝ (flowSeq Φ q r w) s :=
    fun r w s => (((contDiff_flowSeq hΦ.contDiff r w).comp (contDiff_id.prodMk
      contDiff_const)).differentiable one_ne_zero) s
  -- the derivative of the flow in the state is a unit
  have hunit : ∀ j t y, IsUnit (fderiv ℝ (Φ j t) y) := by
    intro j t y
    have hc1 : (Φ j (-t)) ∘ (Φ j t) = id := funext fun x => hΦ.neg_comp j t x
    have hc2 : (Φ j t) ∘ (Φ j (-t)) = id := funext fun x => by
      simpa using hΦ.neg_comp j (-t) x
    have hBA : (fderiv ℝ (Φ j (-t)) (Φ j t y)).comp (fderiv ℝ (Φ j t) y) = 1 := by
      rw [← fderiv_comp y (hdS j (-t) _) (hdS j t y), hc1, fderiv_id]
      rfl
    have hAB : (fderiv ℝ (Φ j t) y).comp (fderiv ℝ (Φ j (-t)) (Φ j t y)) = 1 := by
      have h := fderiv_comp (Φ j t y) (hdS j t (Φ j (-t) (Φ j t y))) (hdS j (-t) (Φ j t y))
      rw [hc2, fderiv_id, hΦ.neg_comp] at h
      rw [← h]
      rfl
    exact ⟨⟨_, _, hAB, hBA⟩, rfl⟩
  -- derivatives along lines
  have hline : ∀ {n : ℕ} {G : (Fin n → ℝ) → E} {a d : Fin n → ℝ} {h : ℝ → E} {v : E},
      DifferentiableAt ℝ G a → (∀ ε : ℝ, G (a + ε • d) = h ε) → HasDerivAt h v 0 →
        fderiv ℝ G a d = v := by
    intro n G a d h v hG hl hh
    have hc : HasDerivAt (fun ε : ℝ => a + ε • d) d 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add a
    have h1 := hG.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
    rw [show (G ∘ fun ε : ℝ => a + ε • d) = h from funext hl] at h1
    exact h1.unique hh
  have hlineT : ∀ r (w : Fin r → Fin m) (s v : Fin r → ℝ),
      HasDerivAt (fun ε : ℝ => flowSeq Φ q r w (s + ε • v)) (fderiv ℝ (flowSeq Φ q r w) s v) 0 := by
    intro r w s v
    have hc : HasDerivAt (fun ε : ℝ => s + ε • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add s
    exact (hdT r w s).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  -- the derivative of one more factor
  have hsnocA : ∀ r (w : Fin r → Fin m) (s : Fin r → ℝ) (j : Fin m) (σ : ℝ) (v : Fin r → ℝ),
      fderiv ℝ (flowSeq Φ q (r + 1) (Fin.snoc w j)) (Fin.snoc s σ) (Fin.snoc v 0) =
        fderiv ℝ (Φ j σ) (flowSeq Φ q r w s) (fderiv ℝ (flowSeq Φ q r w) s v) := by
    intro r w s j σ v
    refine hline (hdT _ _ _) (h := fun ε => Φ j σ (flowSeq Φ q r w (s + ε • v))) (fun ε => ?_) ?_
    · have he : Fin.snoc s σ + ε • Fin.snoc v 0 = (Fin.snoc (s + ε • v) σ : Fin (r + 1) → ℝ) := by
        ext i
        refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
      rw [he, flowSeq_snoc]
    · exact (hdS j σ _).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hlineT r w s v) (by simp)
  have hsnocB : ∀ r (w : Fin r → Fin m) (s : Fin r → ℝ) (j : Fin m) (σ : ℝ),
      fderiv ℝ (flowSeq Φ q (r + 1) (Fin.snoc w j)) (Fin.snoc s σ) (Fin.snoc 0 1) =
        X j (Φ j σ (flowSeq Φ q r w s)) := by
    intro r w s j σ
    refine hline (hdT _ _ _) (h := fun ε => Φ j (σ + ε) (flowSeq Φ q r w s)) (fun ε => ?_) ?_
    · have he : Fin.snoc s σ + ε • Fin.snoc 0 1 = (Fin.snoc s (σ + ε) : Fin (r + 1) → ℝ) := by
        ext i
        refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
      rw [he, flowSeq_snoc]
    · exact HasDerivAt.comp_const_add σ 0 (by simpa using hΦ.hasDerivAt j σ (flowSeq Φ q r w s))
  -- ranges
  have hmapLe : ∀ r (w : Fin r → Fin m) (s : Fin r → ℝ) (j : Fin m) (σ : ℝ),
      (fderiv ℝ (flowSeq Φ q r w) s).range.map (fderiv ℝ (Φ j σ) (flowSeq Φ q r w s)).toLinearMap ≤
        (fderiv ℝ (flowSeq Φ q (r + 1) (Fin.snoc w j)) (Fin.snoc s σ)).range := by
    rintro r w s j σ _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨Fin.snoc v 0, hsnocA r w s j σ v⟩
  have hXmem : ∀ r (w : Fin r → Fin m) (s : Fin r → ℝ) (j : Fin m) (σ : ℝ),
      X j (Φ j σ (flowSeq Φ q r w s)) ∈
        (fderiv ℝ (flowSeq Φ q (r + 1) (Fin.snoc w j)) (Fin.snoc s σ)).range :=
    fun r w s j σ => ⟨Fin.snoc 0 1, hsnocB r w s j σ⟩
  have hinj : ∀ j σ y, Function.Injective (fderiv ℝ (Φ j σ) y) := by
    intro j σ y
    obtain ⟨u, hu⟩ := hunit j σ y
    rw [← hu]
    refine Function.LeftInverse.injective (g := (↑u⁻¹ : E →L[ℝ] E)) fun a => ?_
    exact congrArg (fun T : E →L[ℝ] E => T a) u.inv_mul
  have hfinmap : ∀ r (w : Fin r → Fin m) (s : Fin r → ℝ) (j : Fin m) (σ : ℝ),
      Module.finrank ℝ ((fderiv ℝ (flowSeq Φ q r w) s).range.map
        (fderiv ℝ (Φ j σ) (flowSeq Φ q r w s)).toLinearMap) =
        Module.finrank ℝ (fderiv ℝ (flowSeq Φ q r w) s).range :=
    fun r w s j σ => (Submodule.equivMapOfInjective _ (hinj j σ _) _).finrank_eq.symm
  have hsum : ∀ r (s : Fin r → ℝ) (σ : ℝ),
      ∑ i, |(Fin.snoc s σ : Fin (r + 1) → ℝ) i| = ∑ i, |s i| + |σ| := by
    intro r s σ
    simp [Fin.sum_univ_castSucc]
  -- the maximal rank
  set P : Set ℕ := {k | ∃ r, ∃ w : Fin r → Fin m, ∃ s : Fin r → ℝ, ∑ i, |s i| < δ ∧
    Module.finrank ℝ (fderiv ℝ (flowSeq Φ q r w) s).range = k} with hP
  have hPne : P.Nonempty := ⟨_, 0, fun i => i.elim0, fun i => i.elim0, by simp [hδ], rfl⟩
  have hPbdd : BddAbove P := ⟨Module.finrank ℝ E, by
    rintro _ ⟨r, w, s, -, rfl⟩
    exact Submodule.finrank_le _⟩
  obtain ⟨r₀, w₀, s₀, hs₀, hK⟩ := Nat.sSup_mem hPne hPbdd
  have hmax : ∀ r (w : Fin r → Fin m) (s : Fin r → ℝ), ∑ i, |s i| < δ →
      Module.finrank ℝ (fderiv ℝ (flowSeq Φ q r w) s).range ≤ sSup P :=
    fun r w s hs => le_csSup hPbdd ⟨r, w, s, hs, rfl⟩
  -- one more factor at a point of maximal rank keeps the rank and transports the range
  have hstep : ∀ r (w : Fin r → Fin m) (s : Fin r → ℝ), ∑ i, |s i| < δ →
      Module.finrank ℝ (fderiv ℝ (flowSeq Φ q r w) s).range = sSup P →
      ∀ (j : Fin m) (σ : ℝ), |σ| < δ - ∑ i, |s i| →
        (∑ i, |(Fin.snoc s σ : Fin (r + 1) → ℝ) i| < δ ∧
          Module.finrank ℝ (fderiv ℝ (flowSeq Φ q (r + 1) (Fin.snoc w j)) (Fin.snoc s σ)).range =
            sSup P) ∧
        (fderiv ℝ (flowSeq Φ q r w) s).range.map
            (fderiv ℝ (Φ j σ) (flowSeq Φ q r w s)).toLinearMap =
          (fderiv ℝ (flowSeq Φ q (r + 1) (Fin.snoc w j)) (Fin.snoc s σ)).range := by
    intro r w s hs hrk j σ hσ
    have hs' : ∑ i, |(Fin.snoc s σ : Fin (r + 1) → ℝ) i| < δ := by rw [hsum]; linarith
    have hle := Submodule.finrank_mono (hmapLe r w s j σ)
    rw [hfinmap, hrk] at hle
    have hrk' := le_antisymm (hmax _ _ _ hs') hle
    refine ⟨⟨hs', hrk'⟩, Submodule.eq_of_le_of_finrank_eq (hmapLe r w s j σ) ?_⟩
    rw [hfinmap, hrk, hrk']
  -- every left-normed bracket is tangent at the points of maximal rank
  have htan : ∀ i, ∀ Z ∈ filtrationFields X i, ∀ r (w : Fin r → Fin m) (s : Fin r → ℝ),
      ∑ i, |s i| < δ → Module.finrank ℝ (fderiv ℝ (flowSeq Φ q r w) s).range = sSup P →
        Z (flowSeq Φ q r w s) ∈ (fderiv ℝ (flowSeq Φ q r w) s).range := by
    intro i
    induction i with
    | zero => intro Z hZ; simp [filtrationFields] at hZ
    | succ i ih =>
      rintro Z (⟨j, rfl⟩ | ⟨j, Z', hZ', rfl⟩) r w s hs hrk
      · have h := (hstep r w s hs hrk j 0 (by simpa using hs)).2
        have hid : (fderiv ℝ (Φ j 0) (flowSeq Φ q r w s)).toLinearMap = LinearMap.id := by
          rw [show Φ j 0 = id from funext (hΦ.zero j), fderiv_id]
          rfl
        rw [hid, Submodule.map_id] at h
        rw [h]
        simpa [hΦ.zero] using hXmem r w s j 0
      · set y := flowSeq Φ q r w s with hy
        set L := (fderiv ℝ (flowSeq Φ q r w) s).range with hL
        have hZ'c : ContDiff ℝ ∞ Z' := contDiff_of_mem_filtrationFields hX hZ'
        -- the transported values stay in `L`
        have hin : ∀ σ ∈ Ico (0 : ℝ) (δ - ∑ i, |s i|),
            Ring.inverse (fderiv ℝ (Φ j σ) y) (Z' (Φ j σ y)) ∈ L := by
          intro σ hσ
          have hσ' : |σ| < δ - ∑ i, |s i| := by rw [abs_of_nonneg hσ.1]; exact hσ.2
          obtain ⟨⟨hs', hrk'⟩, hmap⟩ := hstep r w s hs hrk j σ hσ'
          have h := ih Z' hZ' (r + 1) (Fin.snoc w j) (Fin.snoc s σ) hs' hrk'
          rw [flowSeq_snoc, ← hmap] at h
          obtain ⟨l, hl, hlZ⟩ := h
          rw [← hlZ]
          have hcan := Ring.inverse_mul_cancel _ (hunit j σ y)
          have := congrArg (fun T : E →L[ℝ] E => T l) hcan
          change Ring.inverse (fderiv ℝ (Φ j σ) y) ((fderiv ℝ (Φ j σ) y) l) = l at this
          change Ring.inverse (fderiv ℝ (Φ j σ) y) ((fderiv ℝ (Φ j σ) y) l) ∈ L
          rw [this]
          exact hl
        -- the right derivative at `0` is the bracket
        have hA0 : fderiv ℝ (Φ j 0) y = ((1 : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) := by
          rw [show Φ j 0 = id from funext (hΦ.zero j), fderiv_id]
          rfl
        have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (E →L[ℝ] E)ˣ)
        rw [← hA0] at hinv
        have hc := hinv.comp_hasDerivWithinAt (0 : ℝ) (hΦ.hasDerivWithinAt_fderiv j y)
        have hv : HasDerivAt (fun σ => Z' (Φ j σ y)) (fderiv ℝ Z' y (X j y)) 0 := by
          have h0 : HasDerivAt (fun σ => Φ j σ y) (X j y) 0 := by
            simpa [hΦ.zero] using hΦ.hasDerivAt j 0 y
          exact ((hZ'c.differentiable (by simp)) y).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h0
            (hΦ.zero j y).symm
        have hu := hc.clm_apply hv.hasDerivWithinAt
        have hval : lieBracket ℝ (X j) Z' y =
            ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) ↑(1 : (E →L[ℝ] E)ˣ)⁻¹
              ↑(1 : (E →L[ℝ] E)ˣ)⁻¹) (fderiv ℝ (X j) y)) (Z' (Φ j 0 y)) +
              ((Ring.inverse ∘ fun σ => fderiv ℝ (Φ j σ) y) 0) (fderiv ℝ Z' y (X j y)) := by
          simp [lieBracket_eq, hA0, hΦ.zero]
          abel
        rw [← hval] at hu
        -- the limit of difference quotients in the closed subspace `L`
        have hLc : IsClosed (L : Set E) := Submodule.closed_of_finiteDimensional L
        have hslope := hasDerivWithinAt_iff_tendsto_slope.1 hu
        rw [show Ici (0 : ℝ) \ {0} = Ioi 0 by ext x; simp [lt_iff_le_and_ne, eq_comm]] at hslope
        have hε : 0 < δ - ∑ i, |s i| := by linarith
        refine hLc.mem_of_tendsto hslope ?_
        filter_upwards [Ioo_mem_nhdsGT hε] with σ hσ
        rw [slope_def_module]
        refine L.smul_mem _ (L.sub_mem ?_ ?_)
        · exact hin σ ⟨hσ.1.le, hσ.2⟩
        · exact hin 0 ⟨le_rfl, hε⟩
  -- at the point of maximal rank the range is everything
  refine ⟨r₀, w₀, s₀, hs₀, eq_top_iff.2 ?_⟩
  rw [← hspan _ (hW r₀ w₀ s₀ hs₀)]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨Z, hZ, rfl⟩
  obtain ⟨i, hi⟩ := mem_iUnion.1 hZ
  exact htan i Z hi r₀ w₀ s₀ hs₀ hK

/-- **MLS Proposition 7.7, p. 331 ("`(φ^u_{T/2})^{−1}(W)` is a neighborhood of `q₀`"):** on a
finite-dimensional space, if `s ↦ flowSeq Φ q r w s` has a surjective derivative at `s` and the
word `w′` with times `s′` undoes `w` with `s`, then
`s₁ ↦ flowSeq Φ (flowSeq Φ q r w s₁) r w′ s′` maps the neighbourhoods of `s` onto the
neighbourhoods of `q`. -/
theorem map_nhds_flowSeq_undo [FiniteDimensional ℝ E] {Φ : Fin m → ℝ → E → E}
    (hΦ : ∀ j, ContDiff ℝ 1 fun p : ℝ × E => Φ j p.1 p.2) {q : E} {r : ℕ} {w w' : Fin r → Fin m}
    {s s' : Fin r → ℝ} (hs : (fderiv ℝ (flowSeq Φ q r w) s).range = ⊤)
    (hundo : ∀ x, flowSeq Φ (flowSeq Φ x r w s) r w' s' = x) :
    map (fun s₁ => flowSeq Φ (flowSeq Φ q r w s₁) r w' s') (𝓝 s) = 𝓝 q := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  set F := flowSeq Φ q r w with hF
  set Ψ := fun x => flowSeq Φ x r w' s' with hΨ
  have hFc : ContDiff ℝ 1 F :=
    (contDiff_flowSeq hΦ r w).comp (contDiff_id.prodMk contDiff_const)
  have hΨc : ContDiff ℝ 1 Ψ :=
    (contDiff_flowSeq hΦ r w').comp (contDiff_const.prodMk contDiff_id)
  have hFwc : ContDiff ℝ 1 fun x => flowSeq Φ x r w s :=
    (contDiff_flowSeq hΦ r w).comp (contDiff_const.prodMk contDiff_id)
  have hG : ContDiff ℝ 1 (Ψ ∘ F) := hΨc.comp hFc
  have hFq : F s = flowSeq Φ q r w s := rfl
  -- the undoing map has a surjective derivative at `F s`
  have hΨtop : ∀ v : E, ∃ a, fderiv ℝ Ψ (F s) a = v := by
    intro v
    have hc : Ψ ∘ (fun x => flowSeq Φ x r w s) = id := funext hundo
    have h := fderiv_comp q ((hΨc.differentiable one_ne_zero) _)
      ((hFwc.differentiable one_ne_zero) q)
    rw [hc, fderiv_id] at h
    refine ⟨fderiv ℝ (fun x => flowSeq Φ x r w s) q v, ?_⟩
    have h' := congrArg (fun T : E →L[ℝ] E => T v) h
    exact h'.symm
  have hrange : (fderiv ℝ (Ψ ∘ F) s).range = ⊤ := by
    rw [fderiv_comp s ((hΨc.differentiable one_ne_zero) _) ((hFc.differentiable one_ne_zero) s)]
    refine eq_top_iff.2 fun v _ => ?_
    obtain ⟨a, ha⟩ := hΨtop v
    have hamem : a ∈ (fderiv ℝ F s).range := by rw [hs]; trivial
    obtain ⟨b, hb⟩ := hamem
    have hb' : fderiv ℝ F s b = a := hb
    exact ⟨b, by simp [hb', ha]⟩
  have hmap := (hG.hasStrictFDerivAt one_ne_zero).map_nhds_eq_of_surj hrange
  have hGs : (Ψ ∘ F) s = q := hundo q
  rw [hGs] at hmap
  exact hmap

end Nonholonomic
end RoboLean
