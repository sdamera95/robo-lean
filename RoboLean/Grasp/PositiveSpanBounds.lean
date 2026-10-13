import RoboLean.Grasp.Frictionless
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Bounds on the number of contacts: Theorem 5.4 and a weak form of Theorem 5.5

MLS Chapter 5, §4.1, printed p. 230:

* **Theorem 5.4** (printed name "Caratheodory"): "If a set `X = {v₁, …, v_k}` positively spans
  `ℝ^p`, then `k ≥ p + 1`." Here for a finite family `v : ι → W` in a finite-dimensional real
  vector space `W` of dimension `p`, with the added hypothesis `p ≥ 1`: the printed statement is
  false for `p = 0`, where the empty family positively spans `ℝ⁰ = {0}`. The printed name does
  not match Mathlib's Carathéodory theorem (an upper bound on supports in convex hulls); the
  lower bound is Davis's (Amer. J. Math. 76, 1954, Theorem 3.7, as cited by Hare and Song,
  arXiv 1509.07496; secondary citation).
* Its consequence on pp. 230–231: a force-closure grasp of frictionless point contacts has at
  least `p + 1` contacts, `4` in the plane (`p = 3`) and `7` in space (`p = 6`).
* **Theorem 5.5** (Steinitz): "If `S ⊂ ℝ^p` and `q ∈ int(co S)`, then there exists
  `X = {v₁, …, v_k} ⊂ S` such that `q ∈ int(co X)` and `k ≤ 2p`." Here only the weaker bound
  `k ≤ (p + 1)²`, from Mathlib's simplex lemma `exists_mem_interior_convexHull_affineBasis` and
  Carathéodory's theorem `convexHull_eq_union`; the printed constant `2p` is not proved in this
  module.
* Proposition 5.3 (2) ⇔ (3) (p. 226) restated for a finite family of vectors in `κ → ℝ`.

Conventions. "Positively spans" is the library's `PositivelySpans` (MLS p. 225, strictly positive
coefficients, `positivelySpans_iff_nonneg`). `ℝ^p` is any finite-dimensional real vector space
for Theorem 5.4 and any finite-dimensional real normed space for Theorem 5.5; the printed
`ℝ^p` is `Fin p → ℝ`. `co S` is Mathlib's `convexHull ℝ S` and `int` is `interior`. A family may
repeat vectors, so the bounds count members of the family; a `Finset` version is given.
Finite-force caveat: force-closure assumes unbounded contact forces at maintained rigid contacts
(MLS p. 214).
-/

noncomputable section

open Matrix

namespace RoboLean.Grasp

variable {ι W : Type*} [Fintype ι] [AddCommGroup W] [Module ℝ W]

/-- A family that positively spans (MLS printed p. 225) spans: its linear span is the whole
space (supporting lemma for MLS Theorem 5.4, printed p. 230). -/
theorem PositivelySpans.span_eq_top {v : ι → W} (h : PositivelySpans v) :
    Submodule.span ℝ (Set.range v) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨α, -, hx⟩ := h x
  rw [← hx]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **MLS Theorem 5.4**, printed p. 230 (printed name "Caratheodory"): a finite family that
positively spans (p. 225) a real vector space of finite dimension `p ≥ 1` has at least `p + 1`
members. Added hypothesis: `p ≥ 1` (`0 < finrank`); for `p = 0` the empty family positively
spans and the printed bound fails. The proof: positive spanning gives linear spanning, so
`p ≤ k`; with `k = p` the family would be a basis, against the positive dependence
`∑ αᵢ vᵢ = 0`, `αᵢ > 0` (p. 225). -/
theorem PositivelySpans.finrank_succ_le_card [FiniteDimensional ℝ W] {v : ι → W}
    (h : PositivelySpans v) (hW : 0 < Module.finrank ℝ W) :
    Module.finrank ℝ W + 1 ≤ Fintype.card ι := by
  have hspan := h.span_eq_top
  have hle : Module.finrank ℝ W ≤ Fintype.card ι := by
    have hr := finrank_range_le_card (R := ℝ) v
    rwa [Set.finrank, hspan, finrank_top] at hr
  refine Nat.succ_le_of_lt (lt_of_le_of_ne hle fun heq => ?_)
  have hli := linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge heq.symm
  obtain ⟨α, hα, hsum⟩ := h.positivelyDependent
  obtain ⟨i⟩ : Nonempty ι := Fintype.card_pos_iff.mp (heq ▸ hW)
  exact (hα i).ne' (Fintype.linearIndependent_iff.mp hli α hsum i)

/-- **MLS Theorem 5.4**, printed p. 230, as printed: if `v₁, …, v_k` positively span `ℝ^p`
(here `Fin p → ℝ`) and `p ≥ 1`, then `k ≥ p + 1`. Added hypothesis `p ≥ 1`, as for
`PositivelySpans.finrank_succ_le_card`. -/
theorem PositivelySpans.succ_le {p k : ℕ} {v : Fin k → Fin p → ℝ} (h : PositivelySpans v)
    (hp : 1 ≤ p) : p + 1 ≤ k := by
  have hW : 0 < Module.finrank ℝ (Fin p → ℝ) := by
    rw [Module.finrank_fin_fun]
    exact hp
  simpa using h.finrank_succ_le_card hW

/-- **MLS Theorem 5.4**, printed p. 230, for a finite set `X = {v₁, …, v_k}` of vectors (its
elements as a family): if `X` positively spans a real vector space of finite dimension `p ≥ 1`,
then `|X| ≥ p + 1`. Added hypothesis `p ≥ 1`. -/
theorem PositivelySpans.finrank_succ_le_finset_card [FiniteDimensional ℝ W] {X : Finset W}
    (h : PositivelySpans fun x : X => (x : W)) (hW : 0 < Module.finrank ℝ W) :
    Module.finrank ℝ W + 1 ≤ X.card := by
  simpa using h.finrank_succ_le_card hW

/-- **MLS printed pp. 230–231** (consequence of Theorem 5.4 with Proposition 5.3): a
force-closure grasp of frictionless point contacts with grasp matrix `G ∈ ℝ^{p×k}`
(friction cone the orthant of p. 224) has at least `p + 1` contacts (columns), for `p ≥ 1`
(at least one row; the hypothesis MLS does not state). Finite-force caveat: unbounded contact
forces at maintained rigid contacts (MLS p. 214). -/
theorem ForceClosure.card_succ_le_card {κ : Type*} [Fintype κ] [Nonempty κ] [DecidableEq ι]
    {G : Matrix κ ι ℝ} (h : ForceClosure G.mulVecLin (orthantCone ι)) :
    Fintype.card κ + 1 ≤ Fintype.card ι := by
  have hp := (forceClosure_mulVecLin_iff_positivelySpans G).mp h
  have hW : 0 < Module.finrank ℝ (κ → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_pos
  simpa using hp.finrank_succ_le_card hW

/-- **MLS printed p. 231**, `p = 3 (planar) ⟹ 4 ≤ k`: a force-closure planar grasp of `k`
frictionless point contacts, with grasp matrix `G ∈ ℝ^{3×k}` in planar wrench coordinates
`(f_x, f_y, τ)` (p. 222) and the orthant cone of p. 224, has `k ≥ 4`. Finite-force caveat:
unbounded contact forces at maintained rigid contacts (MLS p. 214). -/
theorem four_le_of_forceClosure_planar {k : ℕ} {G : Matrix (Fin 3) (Fin k) ℝ}
    (h : ForceClosure G.mulVecLin (orthantCone (Fin k))) : 4 ≤ k := by
  simpa using ForceClosure.card_succ_le_card h

/-- **MLS printed p. 231**, `p = 6 (spatial) ⟹ 7 ≤ k`: a force-closure spatial grasp of
frictionless point contacts (Example 5.1, p. 220) with any contact frames `g_{ocᵢ}` has at least
`7` contacts. Finite-force caveat: unbounded contact forces at maintained rigid contacts
(MLS p. 214). -/
theorem seven_le_card_of_spatial_frictionless_isForceClosure [DecidableEq ι]
    (frame : ι → RigidTransform)
    (h : (ContactGrasp.spatial (fun _ => ContactModel.frictionless) frame).toGrasp.IsForceClosure) :
    7 ≤ Fintype.card ι := by
  have hp := (spatial_frictionless_isForceClosure_iff frame).mp h
  have hc := hp.finrank_succ_le_card (by rw [Wrench.finrank_eq_six]; norm_num)
  rwa [Wrench.finrank_eq_six] at hc

/-- MLS Proposition 5.3, (2) ⇔ (3), printed p. 226, for a nonempty finite family `v` of vectors
in `κ → ℝ` (product topology): `v` positively spans (p. 225) if and only if the convex hull of
its members contains a neighborhood of the origin. `frictionless_tfae` applied to the matrix
with columns `vᵢ`. -/
theorem positivelySpans_iff_convexHull_mem_nhds {κ : Type*} [Fintype κ] [Nonempty ι]
    (v : ι → κ → ℝ) : PositivelySpans v ↔ convexHull ℝ (Set.range v) ∈ nhds (0 : κ → ℝ) := by
  classical
  have hcol : (Matrix.of fun r i => v i r).col = v := by
    funext i r
    rfl
  have h := frictionless_tfae (Matrix.of fun r i => v i r)
  rw [hcol] at h
  exact h.out 2 3

/-- **MLS Theorem 5.5 (Steinitz), printed p. 230, with the weaker bound `(p + 1)²`**: if
`q ∈ int(co S)` in a real normed space of finite dimension `p`, there is a finite `X ⊂ S` with
`q ∈ int(co X)` and `|X| ≤ (p + 1)²`. The printed bound is `|X| ≤ 2p` (for `p ≥ 1`); this
module does not prove it. Proof: a simplex with `p + 1` vertices around `q` inside `co S`
(Mathlib `exists_mem_interior_convexHull_affineBasis`), each vertex in the hull of at most
`p + 1` points of `S` (Carathéodory, `convexHull_eq_union` with
`AffineIndependent.card_le_finrank_succ`). -/
theorem exists_finset_mem_interior_convexHull_card_le_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {S : Set E} {q : E}
    (hq : q ∈ interior (convexHull ℝ S)) :
    ∃ X : Finset E, (X : Set E) ⊆ S ∧ X.card ≤ (Module.finrank ℝ E + 1) ^ 2 ∧
      q ∈ interior (convexHull ℝ (X : Set E)) := by
  classical
  have hS : convexHull ℝ S ∈ nhds q :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hq) interior_subset
  obtain ⟨b, hbq, hbS⟩ := exists_mem_interior_convexHull_affineBasis hS
  -- each vertex of the simplex is in the hull of at most `p + 1` points of `S` (Carathéodory)
  have hb : ∀ i, ∃ t : Finset E, (t : Set E) ⊆ S ∧ t.card ≤ Module.finrank ℝ E + 1 ∧
      b i ∈ convexHull ℝ (t : Set E) := by
    intro i
    have hi : b i ∈ convexHull ℝ S := hbS (subset_convexHull ℝ _ ⟨i, rfl⟩)
    rw [convexHull_eq_union] at hi
    simp only [Set.mem_iUnion] at hi
    obtain ⟨t, htS, hti, hbt⟩ := hi
    refine ⟨t, htS, ?_, hbt⟩
    have hc := hti.card_le_finrank_succ
    rw [Fintype.card_coe] at hc
    exact hc.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  choose t htS htc hbt using hb
  refine ⟨Finset.univ.biUnion t, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
      Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    exact htS i hi
  · calc (Finset.univ.biUnion t).card ≤ ∑ i, (t i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin (Module.finrank ℝ E + 1), (Module.finrank ℝ E + 1) :=
        Finset.sum_le_sum fun i _ => htc i
      _ = (Module.finrank ℝ E + 1) ^ 2 := by simp [sq]
  · refine interior_mono (convexHull_min ?_ (convex_convexHull ℝ _)) hbq
    rintro _ ⟨i, rfl⟩
    exact convexHull_mono
      (Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem t (Finset.mem_univ i))) (hbt i)

end RoboLean.Grasp
