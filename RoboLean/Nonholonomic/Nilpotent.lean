import RoboLean.Nonholonomic.Filtration
import RoboLean.Nonholonomic.PhilipHall
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Lie products, their length and nilpotency: MLS p. 344

MLS Chapter 7, Section 4.3, printed p. 344: "we define the length of a Lie product recursively as
`l(gᵢ) = 1`, `l([A, B]) = l(A) + l(B)` … A Lie algebra is nilpotent if there exists an integer `k`
such that all Lie products of length greater than `k` are zero. The integer `k` is called the
order of nilpotency." Chapter 8 uses the phrase "nilpotent of degree `k`" for the same notion
(p. 378, Example 8.5; p. 379, Example 8.6; Exercises 1–2, p. 391).

**What is formalized.**
* `IsLieProduct g l A`: `A` is a Lie product of the generators `g` of length `l` (every
  bracketing, not only the right-normed brackets of the filtration of p. 340).
* `IsNilpotentOfOrder g k`: every Lie product of length greater than `k` is the zero field;
  `IsNilpotencyOrder g k` adds that some Lie product of length `k` is nonzero, so that `k` is the
  least such integer (the reading of "of degree `k`" used here).
* `IsLieProduct g l A` holds exactly when `A` is the evaluation of a formal Lie product of length
  `l` (`LieProduct.eval`, `LieProduct.length` of the library's Philip Hall module), so nilpotency
  can be read on formal products.
* The fields spanning the filtration level `Δᵢ` are Lie products of length at most `i`.
* For the polynomial examples of Chapter 8 on `ℝⁿ⁺²`: fields `q ↦ G(q₁, q₂)` that depend only on
  the first two coordinates (`baseField`), the bracket of two such fields through the partial
  derivatives of `G`, and the vanishing of brackets between fields whose values have zero first
  two coordinates.

Coordinates: index `0` is `q₁` and index `1` is `q₂`. The bracket is Mathlib's `lieBracket`,
`[f, g] = (∂g/∂q) f − (∂f/∂q) g`, the convention of MLS p. 323.
-/

open Set Filter Topology VectorField

/-- A derivative of a one-variable polynomial expression in closed form (supporting tactic for the
brackets of MLS pp. 378–379 and 391): differentiability by `fun_prop`, the derivative by `simp`. -/
macro "poly_hasDerivAt" : tactic => `(tactic|
  (refine (DifferentiableAt.hasDerivAt (by fun_prop)).congr_deriv ?_
   first | (simp; done) | (simp; ring) | ring))

namespace RoboLean
namespace Nonholonomic

section LieProduct

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- **MLS p. 344: Lie products of the generators and their length,** `l(gᵢ) = 1` and
`l([A, B]) = l(A) + l(B)`. -/
inductive IsLieProduct (g : Fin m → E → E) : ℕ → (E → E) → Prop
  /-- A generator has length one (MLS p. 344). -/
  | gen (j : Fin m) : IsLieProduct g 1 (g j)
  /-- The bracket of products of lengths `a` and `b` has length `a + b` (MLS p. 344). -/
  | bracket {a b : ℕ} {A B : E → E} : IsLieProduct g a A → IsLieProduct g b B →
      IsLieProduct g (a + b) (lieBracket ℝ A B)

/-- **MLS p. 344: nilpotent of order `k`,** all Lie products of length greater than `k` are zero. -/
def IsNilpotentOfOrder (g : Fin m → E → E) (k : ℕ) : Prop :=
  ∀ l A, IsLieProduct g l A → k < l → A = 0

/-- **MLS p. 344 ("the order of nilpotency") and pp. 378–379, 391 ("nilpotent of degree `k`"):**
nilpotent of order `k`, with some Lie product of length `k` nonzero, so that `k` is the least such
integer. -/
def IsNilpotencyOrder (g : Fin m → E → E) (k : ℕ) : Prop :=
  IsNilpotentOfOrder g k ∧ ∃ A, IsLieProduct g k A ∧ A ≠ 0

/-- **MLS p. 344:** every Lie product has length at least one. -/
theorem IsLieProduct.one_le {g : Fin m → E → E} {l : ℕ} {A : E → E} (h : IsLieProduct g l A) :
    1 ≤ l := by
  induction h with
  | gen j => exact le_rfl
  | bracket _ _ ha _ => omega

/-- **MLS p. 344: Lie products as evaluated formal products:** `A` is a Lie product of length `l`
exactly when it is the field of a formal Lie product of length `l`. -/
theorem isLieProduct_iff {g : Fin m → E → E} {l : ℕ} {A : E → E} :
    IsLieProduct g l A ↔ ∃ P : LieProduct m, P.length = l ∧ P.eval g = A := by
  constructor
  · intro h
    induction h with
    | gen j => exact ⟨LieProduct.gen j, rfl, rfl⟩
    | bracket _ _ iha ihb =>
      obtain ⟨P, hP, rfl⟩ := iha
      obtain ⟨Q, hQ, rfl⟩ := ihb
      exact ⟨LieProduct.br P Q, by simp [LieProduct.length, hP, hQ], rfl⟩
  · rintro ⟨P, rfl, rfl⟩
    induction P with
    | gen j => exact IsLieProduct.gen j
    | br P Q ihP ihQ => exact IsLieProduct.bracket ihP ihQ

/-- **MLS p. 344: nilpotency on formal products:** nilpotent of order `k` exactly when every
formal Lie product of length greater than `k` evaluates to the zero field. -/
theorem isNilpotentOfOrder_iff {g : Fin m → E → E} {k : ℕ} :
    IsNilpotentOfOrder g k ↔ ∀ P : LieProduct m, k < P.length → P.eval g = 0 := by
  constructor
  · intro h P hP
    exact h P.length (P.eval g) (isLieProduct_iff.2 ⟨P, rfl, rfl⟩) hP
  · intro h l A hA hl
    obtain ⟨P, rfl, rfl⟩ := isLieProduct_iff.1 hA
    exact h P hl

/-- **MLS p. 344:** nilpotent of order `k` implies nilpotent of every larger order. -/
theorem IsNilpotentOfOrder.mono {g : Fin m → E → E} {k k' : ℕ} (h : IsNilpotentOfOrder g k)
    (hk : k ≤ k') : IsNilpotentOfOrder g k' :=
  fun l A hA hl => h l A hA (lt_of_le_of_lt hk hl)

/-- **MLS p. 344: the order of nilpotency is unique** (the least `k`). -/
theorem IsNilpotencyOrder.unique {g : Fin m → E → E} {k k' : ℕ} (h : IsNilpotencyOrder g k)
    (h' : IsNilpotencyOrder g k') : k = k' := by
  obtain ⟨hn, A, hA, hA0⟩ := h
  obtain ⟨hn', A', hA', hA0'⟩ := h'
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exact absurd (hn k' A' hA' hlt) hA0'
  · exact heq
  · exact absurd (hn' k A hA hgt) hA0

/-- **MLS pp. 340 and 344:** the fields spanning `Δᵢ` are Lie products of length between `1` and
`i`. -/
theorem isLieProduct_of_mem_filtrationFields {g : Fin m → E → E} {i : ℕ} {f : E → E}
    (hf : f ∈ filtrationFields g i) : ∃ l, 1 ≤ l ∧ l ≤ i ∧ IsLieProduct g l f := by
  induction i generalizing f with
  | zero => simp [filtrationFields] at hf
  | succ i ih =>
    rcases hf with ⟨j, rfl⟩ | ⟨j, w, hw, rfl⟩
    · exact ⟨1, le_rfl, by omega, IsLieProduct.gen j⟩
    · obtain ⟨l, hl1, hli, hl⟩ := ih hw
      exact ⟨1 + l, by omega, by omega, IsLieProduct.bracket (IsLieProduct.gen j) hl⟩

/-- **MLS p. 344:** a nilpotent system with `Δᵢ` spanned by products of length at most `i`: if every
Lie product of length at most `i` has its value at `q` in a subspace `V`, then `Δᵢ(q) ≤ V`. -/
theorem filtrationAt_le_of_isLieProduct {g : Fin m → E → E} {i : ℕ} {q : E} {V : Submodule ℝ E}
    (h : ∀ l A, IsLieProduct g l A → l ≤ i → A q ∈ V) : filtrationAt g i q ≤ V := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨l, -, hli, hl⟩ := isLieProduct_of_mem_filtrationFields hf
  exact h l f hl hli

end LieProduct

section BaseFields

variable {n : ℕ}

/-- **Fields depending on `q₁, q₂` only** (the polynomial examples of MLS pp. 378–379 and 391):
`X(q + v) = X(q)` whenever `v` has zero first two coordinates. -/
def IsBase (X : (Fin (n + 2) → ℝ) → Fin (n + 2) → ℝ) : Prop :=
  ∀ q v : Fin (n + 2) → ℝ, v 0 = 0 → v 1 = 0 → X (q + v) = X q

/-- **The field `q ↦ G(q₁, q₂)`** on `ℝⁿ⁺²` built from a map of the first two coordinates
(MLS pp. 378–379 and 391; index `0` is `q₁`, index `1` is `q₂`). -/
def baseField (G : ℝ → ℝ → Fin (n + 2) → ℝ) (q : Fin (n + 2) → ℝ) : Fin (n + 2) → ℝ :=
  G (q 0) (q 1)

/-- **`q ↦ G(q₁, q₂)` depends on `q₁, q₂` only** (MLS pp. 378–379, 391). -/
theorem isBase_baseField (G : ℝ → ℝ → Fin (n + 2) → ℝ) : IsBase (baseField G) := by
  intro q v h0 h1
  simp [baseField, h0, h1]

/-- **A constant field is a field of `q₁, q₂` only** (MLS pp. 378–379, 391). -/
theorem isBase_const (v : Fin (n + 2) → ℝ) : IsBase (fun _ : Fin (n + 2) → ℝ => v) :=
  fun _ _ _ _ => rfl

/-- **The derivative of a field of `q₁, q₂` vanishes on vectors with zero first two coordinates**
(supporting lemma for MLS p. 344; no differentiability is needed, since a nondifferentiable field
has zero `fderiv`). -/
theorem fderiv_apply_eq_zero_of_isBase {X : (Fin (n + 2) → ℝ) → Fin (n + 2) → ℝ} (hX : IsBase X)
    (q : Fin (n + 2) → ℝ) {v : Fin (n + 2) → ℝ} (h0 : v 0 = 0) (h1 : v 1 = 0) :
    fderiv ℝ X q v = 0 := by
  by_cases hd : DifferentiableAt ℝ X q
  · have hl : HasDerivAt (fun t : ℝ => q + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
    have hX' : HasFDerivAt X (fderiv ℝ X q) (q + (0 : ℝ) • v) := by simpa using hd.hasFDerivAt
    have h := hX'.comp_hasDerivAt (0 : ℝ) hl
    have hc : (X ∘ fun t : ℝ => q + t • v) = fun _ => X q := by
      funext t
      exact hX q (t • v) (by simp [h0]) (by simp [h1])
    rw [hc] at h
    exact h.unique (hasDerivAt_const _ _)
  · rw [fderiv_zero_of_not_differentiableAt hd]
    rfl

/-- **Brackets of fields of `q₁, q₂` with values of zero first two coordinates vanish**
(MLS p. 344, used for the nilpotency of the systems of Exercises 1–2, p. 391). -/
theorem lieBracket_eq_zero_of_isBase {X Y : (Fin (n + 2) → ℝ) → Fin (n + 2) → ℝ} (hX : IsBase X)
    (hY : IsBase Y) (q : Fin (n + 2) → ℝ) (hX0 : X q 0 = 0) (hX1 : X q 1 = 0) (hY0 : Y q 0 = 0)
    (hY1 : Y q 1 = 0) : lieBracket ℝ X Y q = 0 := by
  show fderiv ℝ Y q (X q) - fderiv ℝ X q (Y q) = 0
  rw [fderiv_apply_eq_zero_of_isBase hY q hX0 hX1, fderiv_apply_eq_zero_of_isBase hX q hY0 hY1,
    sub_zero]

/-- **The bracket of a field of `q₁, q₂` with a constant field of zero first two coordinates
vanishes** (MLS p. 344, Exercises 1–2, p. 391). -/
theorem lieBracket_const_eq_zero_of_isBase {X : (Fin (n + 2) → ℝ) → Fin (n + 2) → ℝ}
    (hX : IsBase X) {v : Fin (n + 2) → ℝ} (h0 : v 0 = 0) (h1 : v 1 = 0) :
    lieBracket ℝ X (fun _ => v) = 0 := by
  funext q
  show fderiv ℝ (fun _ => v) q (X q) - fderiv ℝ X q v = 0
  rw [fderiv_apply_eq_zero_of_isBase hX q h0 h1]
  simp

/-- **The derivative of `q ↦ G(q₁, q₂)` through partial derivatives** (supporting lemma for MLS
pp. 344, 391): if the field is differentiable at `q` and `Gₐ, G_b` are the partial derivatives of
`G` at `(q₁, q₂)`, then `DX(q) v = v₁ Gₐ + v₂ G_b`. -/
theorem fderiv_baseField_apply {G : ℝ → ℝ → Fin (n + 2) → ℝ} {q : Fin (n + 2) → ℝ}
    (hG : DifferentiableAt ℝ (baseField G) q) {Ga Gb : Fin (n + 2) → ℝ}
    (hGa : HasDerivAt (fun a => G a (q 1)) Ga (q 0)) (hGb : HasDerivAt (fun b => G (q 0) b) Gb (q 1))
    (v : Fin (n + 2) → ℝ) :
    fderiv ℝ (baseField G) q v = v 0 • Ga + v 1 • Gb := by
  set e0 : Fin (n + 2) → ℝ := Pi.single 0 1
  set e1 : Fin (n + 2) → ℝ := Pi.single 1 1
  have h01 : (1 : Fin (n + 2)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hdec : v = v 0 • e0 + v 1 • e1 + (v - v 0 • e0 - v 1 • e1) := by abel
  have hw0 : (v - v 0 • e0 - v 1 • e1) 0 = 0 := by simp [e0, e1, h01.symm]
  have hw1 : (v - v 0 • e0 - v 1 • e1) 1 = 0 := by simp [e0, e1, h01]
  have hline : ∀ (w : Fin (n + 2) → ℝ) (G' : Fin (n + 2) → ℝ),
      HasDerivAt (fun t : ℝ => baseField G (q + t • w)) G' 0 → fderiv ℝ (baseField G) q w = G' := by
    intro w G' h
    have hl : HasDerivAt (fun t : ℝ => q + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add q
    have hG' : HasFDerivAt (baseField G) (fderiv ℝ (baseField G) q) (q + (0 : ℝ) • w) := by
      rw [zero_smul, add_zero]
      exact hG.hasFDerivAt
    have hc := hG'.comp_hasDerivAt (0 : ℝ) hl
    rw [Function.comp_def] at hc
    exact hc.unique h
  have hd0 : fderiv ℝ (baseField G) q e0 = Ga := by
    apply hline
    have hs : HasDerivAt (fun t : ℝ => q 0 + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (q 0)
    have hc := hGa.scomp_of_eq (0 : ℝ) hs (by simp)
    have hf : (fun t : ℝ => baseField G (q + t • e0)) = (fun a => G a (q 1)) ∘ fun t => q 0 + t := by
      funext t
      simp [baseField, e0, h01]
    rw [hf]
    simpa using hc
  have hd1 : fderiv ℝ (baseField G) q e1 = Gb := by
    apply hline
    have hs : HasDerivAt (fun t : ℝ => q 1 + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (q 1)
    have hc := hGb.scomp_of_eq (0 : ℝ) hs (by simp)
    have hf : (fun t : ℝ => baseField G (q + t • e1)) = (fun b => G (q 0) b) ∘ fun t => q 1 + t := by
      funext t
      simp [baseField, e1, h01.symm]
    rw [hf]
    simpa using hc
  conv_lhs => rw [hdec]
  rw [map_add, map_add, map_smul, map_smul, hd0, hd1,
    fderiv_apply_eq_zero_of_isBase (isBase_baseField G) q hw0 hw1, add_zero]

/-- **The bracket of two fields of `q₁, q₂` through partial derivatives** (MLS p. 323 convention
`[F, G] = (∂G/∂q)F − (∂F/∂q)G`, used for the brackets of Exercises 1–2, p. 391):
`[F, G](q) = F₁ Gₐ + F₂ G_b − G₁ Fₐ − G₂ F_b` with all values at `(q₁, q₂)`. -/
theorem lieBracket_baseField {F G : ℝ → ℝ → Fin (n + 2) → ℝ} {q : Fin (n + 2) → ℝ}
    (hF : DifferentiableAt ℝ (baseField F) q) (hG : DifferentiableAt ℝ (baseField G) q)
    {Fa Fb Ga Gb : Fin (n + 2) → ℝ}
    (hFa : HasDerivAt (fun a => F a (q 1)) Fa (q 0)) (hFb : HasDerivAt (fun b => F (q 0) b) Fb (q 1))
    (hGa : HasDerivAt (fun a => G a (q 1)) Ga (q 0)) (hGb : HasDerivAt (fun b => G (q 0) b) Gb (q 1)) :
    lieBracket ℝ (baseField F) (baseField G) q =
      F (q 0) (q 1) 0 • Ga + F (q 0) (q 1) 1 • Gb - (G (q 0) (q 1) 0 • Fa + G (q 0) (q 1) 1 • Fb) := by
  show fderiv ℝ (baseField G) q (baseField F q) - fderiv ℝ (baseField F) q (baseField G q) = _
  rw [fderiv_baseField_apply hG hGa hGb, fderiv_baseField_apply hF hFa hFb]
  rfl

end BaseFields

end Nonholonomic
end RoboLean
