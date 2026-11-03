import RoboLean.Nonholonomic.FiltrationBrackets
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The controllability Lie algebra is spanned by left-normed brackets (MLS pp. 326, 329, 340)

**What MLS prints.** The Lie algebra `L(g₁, …, g_m)` is "obtained by taking all linear
combinations of elements of `g₁, …, g_m`, taking Lie brackets of these, taking all linear
combinations of these, and so on" (p. 326); its rank at `q` is the controllability rank condition
of Theorem 7.5 (p. 329). The filtration `Δᵢ = Δᵢ₋₁ + [Δ₁, Δᵢ₋₁]` (p. 340) uses only the brackets
`[gⱼ, w]` of a generator with a field of the previous level.

**Proved here.**

* For smooth generators every element of `L(g₁, …, g_m)` is a real linear combination of
  left-normed brackets `[g_{j₁}, [g_{j₂}, ⋯ [g_{j_{k−1}}, g_{j_k}] ⋯ ]]`, the fields spanning the
  levels of the filtration (`mem_span_leftNormedFields_of_inLieAlgebra`), by the Jacobi identity
  in its Leibniz form `[[U, V], W] = [U, [V, W]] − [V, [U, W]]`; hence the values of
  `L(g₁, …, g_m)` at `q` are the span of the values of the left-normed brackets
  (`lieAlgebraAt_eq_spanAt_leftNormedFields`), the union of the levels `Δᵢ(q)`.
* Fields equal on an open set have left-normed brackets equal on it
  (`exists_mem_filtrationFields_eqOn`, `spanAt_leftNormedFields_le`).
* On a finite-dimensional space the rank condition is open: if continuous fields span at `q` they
  span at every point near `q` (`eventually_spanAt_eq_top`).

**Conventions.** Those of `Nonholonomic/Filtration` (with `contDiff_of_mem_filtrationFields` from
`Nonholonomic/FiltrationBrackets`): fields `E → E`, Mathlib's bracket
`lieBracket ℝ V W x = DW(x) V(x) − DV(x) W(x)` (the book's sign, p. 323), `C^∞` meaning
`ContDiff ℝ ∞`. `leftNormedFields g` is the union over `i` of `filtrationFields g i`.
-/

noncomputable section

open Set Filter Topology VectorField
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- **MLS p. 340: the left-normed brackets of the generators,** the fields spanning some level
`Δᵢ` of the filtration: the generators and the brackets `[gⱼ, w]` with `w` left-normed. -/
def leftNormedFields (g : Fin m → E → E) : Set (E → E) := ⋃ i, filtrationFields g i

/-- **MLS p. 326 with p. 340 (Jacobi reduction):** for smooth generators every element of the Lie
algebra `L(g₁, …, g_m)` is a real linear combination of left-normed brackets. -/
theorem mem_span_leftNormedFields_of_inLieAlgebra {g : Fin m → E → E}
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) {f : E → E} (hf : InLieAlgebra g f) :
    f ∈ Submodule.span ℝ (leftNormedFields g) := by
  have hsm : ∀ f ∈ Submodule.span ℝ (leftNormedFields g), ContDiff ℝ ∞ f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi⟩ := mem_iUnion.1 hx
      exact contDiff_of_mem_filtrationFields hg hi
    | zero => exact contDiff_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul a x _ hx => exact hx.const_smul a
  have hd : ∀ f ∈ Submodule.span ℝ (leftNormedFields g), ∀ x, DifferentiableAt ℝ f x :=
    fun f hf x => (hsm f hf).differentiable (by simp) x
  have h1 : ∀ j, ∀ b ∈ Submodule.span ℝ (leftNormedFields g),
      lieBracket ℝ (g j) b ∈ Submodule.span ℝ (leftNormedFields g) := by
    intro j b hb
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi⟩ := mem_iUnion.1 hx
      exact Submodule.subset_span (mem_iUnion.2 ⟨i + 1, lieBracket_mem_filtrationFields g j hi⟩)
    | zero => rw [lieBracket_zero_right]; exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      have h : lieBracket ℝ (g j) (x + y) = lieBracket ℝ (g j) x + lieBracket ℝ (g j) y := by
        funext z
        exact lieBracket_add_right (hd x hx z) (hd y hy z)
      rw [h]
      exact Submodule.add_mem _ ihx ihy
    | smul a x hx ihx =>
      have h : lieBracket ℝ (g j) (a • x) = a • lieBracket ℝ (g j) x := by
        funext z
        exact lieBracket_const_smul_right (hd x hx z)
      rw [h]
      exact Submodule.smul_mem _ a ihx
  have h2 : ∀ i, ∀ a ∈ filtrationFields g i, ∀ b ∈ Submodule.span ℝ (leftNormedFields g),
      lieBracket ℝ a b ∈ Submodule.span ℝ (leftNormedFields g) := by
    intro i
    induction i with
    | zero => intro a ha; simp [filtrationFields] at ha
    | succ i ih =>
      rintro a (⟨j, rfl⟩ | ⟨j, w, hw, rfl⟩) b hb
      · exact h1 j b hb
      · have hwS : w ∈ Submodule.span ℝ (leftNormedFields g) :=
          Submodule.subset_span (mem_iUnion.2 ⟨i, hw⟩)
        have hgS : g j ∈ Submodule.span ℝ (leftNormedFields g) :=
          Submodule.subset_span (mem_iUnion.2 ⟨1, by rw [filtrationFields_one]; exact mem_range_self j⟩)
        have key : lieBracket ℝ (lieBracket ℝ (g j) w) b =
            lieBracket ℝ (g j) (lieBracket ℝ w b) - lieBracket ℝ w (lieBracket ℝ (g j) b) := by
          funext z
          have hl := leibniz_identity_lieBracket (𝕜 := ℝ) (n := ∞)
            (by simp [minSmoothness_of_isRCLikeNormedField])
            ((hsm _ hgS).contDiffAt (x := z)) ((hsm w hwS).contDiffAt) ((hsm b hb).contDiffAt)
          simp only [Pi.sub_apply]
          rw [hl]
          abel
        rw [key]
        exact Submodule.sub_mem _ (h1 j _ (ih w hw b hb)) (ih w hw _ (h1 j b hb))
  have h3 : ∀ a ∈ Submodule.span ℝ (leftNormedFields g), ∀ b ∈ Submodule.span ℝ (leftNormedFields g),
      lieBracket ℝ a b ∈ Submodule.span ℝ (leftNormedFields g) := by
    intro a ha b hb
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi⟩ := mem_iUnion.1 hx
      exact h2 i x hi b hb
    | zero => rw [lieBracket_zero_left]; exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      have h : lieBracket ℝ (x + y) b = lieBracket ℝ x b + lieBracket ℝ y b := by
        funext z
        exact lieBracket_add_left (hd x hx z) (hd y hy z)
      rw [h]
      exact Submodule.add_mem _ ihx ihy
    | smul c x hx ihx =>
      have h : lieBracket ℝ (c • x) b = c • lieBracket ℝ x b := by
        funext z
        exact lieBracket_const_smul_left (hd x hx z)
      rw [h]
      exact Submodule.smul_mem _ c ihx
  induction hf with
  | gen j =>
    exact Submodule.subset_span (mem_iUnion.2 ⟨1, by rw [filtrationFields_one]; exact mem_range_self j⟩)
  | add _ _ ihf ihh => exact Submodule.add_mem _ ihf ihh
  | smul c _ ih => exact Submodule.smul_mem _ c ih
  | bracket _ _ ihf ihh => exact h3 _ ihf _ ihh

/-- **MLS pp. 326, 329 and 340: the values of `L(g₁, …, g_m)` at `q` are spanned by the values of
the left-normed brackets** (smooth generators). -/
theorem lieAlgebraAt_eq_spanAt_leftNormedFields {g : Fin m → E → E}
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) (q : E) :
    lieAlgebraAt g q = spanAt (leftNormedFields g) q := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    have h := Submodule.mem_map_of_mem (f := LinearMap.proj (R := ℝ) (φ := fun _ : E => E) q)
      (mem_span_leftNormedFields_of_inLieAlgebra hg hf)
    rw [Submodule.map_span] at h
    exact h
  · exact spanAt_mono (fun f hf => by
      obtain ⟨i, hi⟩ := mem_iUnion.1 hf
      exact filtrationFields_subset_lieAlgebra g i hi) q

/-- **MLS pp. 323 and 340: brackets are local.** If `g′ⱼ = gⱼ` on an open set `B` for every `j`,
then every left-normed bracket of the `gⱼ` of level `i` agrees on `B` with one of the `g′ⱼ` of the
same level. -/
theorem exists_mem_filtrationFields_eqOn {g g' : Fin m → E → E} {B : Set E} (hB : IsOpen B)
    (hgg : ∀ j, EqOn (g' j) (g j) B) {i : ℕ} {f : E → E} (hf : f ∈ filtrationFields g i) :
    ∃ f' ∈ filtrationFields g' i, EqOn f' f B := by
  induction i generalizing f with
  | zero => simp [filtrationFields] at hf
  | succ i ih =>
    rcases hf with ⟨j, rfl⟩ | ⟨j, w, hw, rfl⟩
    · exact ⟨g' j, Or.inl (mem_range_self j), hgg j⟩
    · obtain ⟨w', hw', hww⟩ := ih hw
      refine ⟨lieBracket ℝ (g' j) w', Or.inr ⟨j, w', hw', rfl⟩, fun y hy => ?_⟩
      have hev1 : g' j =ᶠ[𝓝 y] g j := eventually_of_mem (hB.mem_nhds hy) fun z hz => hgg j hz
      have hev2 : w' =ᶠ[𝓝 y] w := eventually_of_mem (hB.mem_nhds hy) fun z hz => hww hz
      exact hev1.lieBracket_vectorField_eq hev2

/-- **MLS p. 340: fields equal on an open set `B` span the same left-normed brackets on `B`** (one
inclusion, at each point of `B`). -/
theorem spanAt_leftNormedFields_le {g g' : Fin m → E → E} {B : Set E} (hB : IsOpen B)
    (hgg : ∀ j, EqOn (g' j) (g j) B) {p : E} (hp : p ∈ B) :
    spanAt (leftNormedFields g) p ≤ spanAt (leftNormedFields g') p := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨i, hi⟩ := mem_iUnion.1 hf
  obtain ⟨f', hf', hff⟩ := exists_mem_filtrationFields_eqOn hB hgg hi
  show f p ∈ _
  rw [← hff hp]
  exact mem_spanAt (mem_iUnion.2 ⟨i, hf'⟩) p

/-- **MLS p. 330 (Proposition 7.6 asks `Δ_q = T_q ℝⁿ` near `q₀`; Theorem 7.5, p. 329, asks it at
`q` only): the rank condition is open.** On a finite-dimensional space, if the values at `q` of a
set `S` of continuous fields span `E`, they span `E` at every point near `q`. -/
theorem eventually_spanAt_eq_top [FiniteDimensional ℝ E] {S : Set (E → E)}
    (hS : ∀ f ∈ S, Continuous f) {q : E} (hq : spanAt S q = ⊤) :
    ∀ᶠ p in 𝓝 q, spanAt S p = ⊤ := by
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℝ ((fun f : E → E => f q) '' S)
  have hbtop : Submodule.span ℝ b = ⊤ := by rw [hbspan]; exact hq
  have hfin : Finite b := hbli.finite
  have : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = Module.finrank ℝ E := by
    have h := finrank_span_eq_card hbli
    rw [Subtype.range_coe_subtype, ofPred_mem_eq, hbtop, finrank_top] at h
    exact h.symm
  choose F hFS hFq using fun v : b => hbsub v.2
  have hcont : Continuous fun p : E => fun v : b => F v p :=
    continuous_pi fun v => hS _ (hFS v)
  have hopen := isOpen_setOfPred_linearIndependent (𝕜 := ℝ) (E := E) (ι := b)
  have hq' : (fun v : b => F v q) ∈ {f : b → E | LinearIndependent ℝ f} := by
    simp only [mem_ofPred_eq, hFq]
    exact hbli
  filter_upwards [hcont.continuousAt.preimage_mem_nhds (hopen.mem_nhds hq')] with p hp
  have hli : LinearIndependent ℝ fun v : b => F v p := hp
  refine eq_top_iff.2 ?_
  have hle : Submodule.span ℝ (range fun v : b => F v p) ≤ spanAt S p :=
    Submodule.span_le.2 (range_subset_iff.2 fun v => Submodule.subset_span ⟨F v, hFS v, rfl⟩)
  have htop : Submodule.span ℝ (range fun v : b => F v p) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hli, hcard])
  rw [← htop]
  exact hle

end Nonholonomic
end RoboLean
