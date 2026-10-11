import RoboLean.Grasp.ForceClosure
import RoboLean.Grasp.GraspMap
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Force-closure of frictionless grasps: positive spans, convex hulls and supporting hyperplanes

MLS Chapter 5, §3.2, printed pp. 224–228: for a fixed contact grasp with only frictionless point
contacts, `FC = {f ∈ ℝ^m : fᵢ ≥ 0}` (p. 224) and force-closure becomes a statement about the
columns `Gᵢ` of the grasp matrix. Definitions of p. 225: a family `v₁, …, v_k` is *positively
dependent* if `∑ αᵢ vᵢ = 0` for some `αᵢ > 0`, and *positively spans* `ℝ^n` if every `x` is
`∑ αᵢ vᵢ` with all `αᵢ > 0` (strict positivity, as printed). Proposition 5.3 (p. 226): for
`G ∈ ℝ^{p×m}` the following are equivalent:

1. the grasp is force-closure;
2. the columns of `G` positively span `ℝ^p`;
3. the convex hull of the columns contains a neighborhood of the origin;
4. there is no `v ∈ ℝ^p`, `v ≠ 0`, with `v · Gᵢ ≥ 0` for every column.

MLS proves (1)⇔(2) ("follows from the definition") and refers (3), (4) to [97]; all four are
proved here. Conventions: columns are indexed by a finite type `ι` (the book's `1, …, m`), rows
by a finite type `κ` (the book's `1, …, p`); `G.col i` is column `i`; `v ⬝ᵥ w` is the dot
product; the topology of `κ → ℝ` is the product topology (the Euclidean topology of `ℝ^p`).
Positive spanning is proved equivalent to the version with nonnegative coefficients
(`positivelySpans_iff_nonneg`). Statement (3) needs at least one column (`[Nonempty ι]`), a
hypothesis MLS does not state: with no columns and `p = 0`, (1) holds and the empty hull is not a
neighborhood. Finite-force caveat: force-closure quantifies over unbounded contact forces at
maintained rigid contacts (MLS p. 214); none of these statements bounds the forces.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace Grasp

variable {ι W : Type*} [Fintype ι] [AddCommGroup W] [Module ℝ W]

/-- A finite family of vectors is positively dependent, MLS printed p. 225: `∑ αᵢ vᵢ = 0` for some
coefficients `αᵢ > 0` (strictly positive, as printed). -/
def PositivelyDependent (v : ι → W) : Prop :=
  ∃ α : ι → ℝ, (∀ i, 0 < α i) ∧ ∑ i, α i • v i = 0

/-- A finite family of vectors positively spans the space, MLS printed p. 225: every `x` is
`∑ αᵢ vᵢ` with all `αᵢ > 0` (strictly positive, as printed; `positivelySpans_iff_nonneg` gives
the nonnegative form). -/
def PositivelySpans (v : ι → W) : Prop :=
  ∀ x : W, ∃ α : ι → ℝ, (∀ i, 0 < α i) ∧ ∑ i, α i • v i = x

/-- MLS printed p. 225: "Any set of vectors which positively spans `ℝⁿ` is positively dependent
(by choosing `x = 0`)." -/
theorem PositivelySpans.positivelyDependent {v : ι → W} (h : PositivelySpans v) :
    PositivelyDependent v :=
  h 0

/-- Positive spanning with strictly positive coefficients (MLS printed p. 225) is equivalent to
spanning with nonnegative coefficients: given the nonnegative form, `-∑ vᵢ` is a nonnegative
combination, which yields a positive dependence `∑ (1 + βᵢ) vᵢ = 0` to add to any nonnegative
representation. -/
theorem positivelySpans_iff_nonneg (v : ι → W) :
    PositivelySpans v ↔ ∀ x : W, ∃ α : ι → ℝ, (∀ i, 0 ≤ α i) ∧ ∑ i, α i • v i = x := by
  constructor
  · intro h x
    obtain ⟨α, hα, hx⟩ := h x
    exact ⟨α, fun i => (hα i).le, hx⟩
  · intro h x
    obtain ⟨β, hβ, hb⟩ := h (-∑ i, v i)
    obtain ⟨α, hα, ha⟩ := h x
    refine ⟨fun i => α i + 1 + β i, fun i => by linarith [hα i, hβ i], ?_⟩
    simp only [add_smul, one_smul, Finset.sum_add_distrib, ha, hb]
    abel

/-- Force-closure (MLS Definition 5.2, printed p. 223) restated without the sign: every wrench
`x` is `G f` for some `f ∈ FC`. -/
private theorem forceClosure_iff_forall_exists {E : Type*} [AddCommGroup E] [Module ℝ E]
    (G : E →ₗ[ℝ] W) (FC : Set E) : ForceClosure G FC ↔ ∀ x : W, ∃ f ∈ FC, G f = x := by
  constructor
  · intro h x
    obtain ⟨f, hf, hGf⟩ := h (-x)
    exact ⟨f, hf, by rw [hGf, neg_neg]⟩
  · intro h Fe
    exact h (-Fe)

/-- A linear map on `ι → ℝ` is the combination of its values on the standard basis. -/
private theorem map_eq_sum_single [DecidableEq ι] (G : (ι → ℝ) →ₗ[ℝ] W) (f : ι → ℝ) :
    G f = ∑ i, f i • G (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single f]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_smul]
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/-- MLS Proposition 5.3, (1) ⇔ (2), printed p. 226, for any linear grasp map on frictionless
contact coefficients `ι → ℝ` with the orthant friction cone `{f : fᵢ ≥ 0}` of p. 224: the grasp is
force-closure if and only if its columns `G eᵢ` positively span the wrench space. Finite-force
caveat: unbounded contact forces, maintained rigid contacts (MLS p. 214). -/
theorem forceClosure_orthantCone_iff_positivelySpans [DecidableEq ι] (G : (ι → ℝ) →ₗ[ℝ] W) :
    ForceClosure G (orthantCone ι) ↔ PositivelySpans fun i => G (Pi.single i 1) := by
  rw [forceClosure_iff_forall_exists, positivelySpans_iff_nonneg]
  refine forall_congr' fun x => ⟨fun ⟨f, hf, hx⟩ => ⟨f, hf, ?_⟩, fun ⟨f, hf, hx⟩ => ⟨f, hf, ?_⟩⟩
  · rw [← hx, map_eq_sum_single G f]
  · rw [map_eq_sum_single G f, hx]

variable {κ : Type*} [Fintype κ]

omit [Fintype κ] in
/-- A matrix times a vector is the combination of the columns with the vector's entries. -/
private theorem mulVec_eq_sum_col [DecidableEq ι] (G : Matrix κ ι ℝ) (f : ι → ℝ) :
    G *ᵥ f = ∑ i, f i • G.col i := by
  have h := map_eq_sum_single G.mulVecLin f
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using h

omit [Fintype κ] in
/-- Each column `Gᵢ = G eᵢ` lies in the image `G(FC)` of the orthant of MLS printed p. 224. -/
private theorem col_mem_image_orthantCone [DecidableEq ι] (G : Matrix κ ι ℝ) (i : ι) :
    G.col i ∈ G.mulVecLin '' (orthantCone ι : Set (ι → ℝ)) := by
  refine ⟨Pi.single i 1, fun j => ?_, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]⟩
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

omit [Fintype κ] in
/-- MLS Proposition 5.3, (1) ⇔ (2), printed p. 226, for a grasp matrix `G ∈ ℝ^{p×m}` of
frictionless point contacts (friction cone the orthant of p. 224): force-closure if and only if
the columns of `G` positively span `ℝ^p`. Finite-force caveat: unbounded contact forces,
maintained rigid contacts (MLS p. 214). -/
theorem forceClosure_mulVecLin_iff_positivelySpans [DecidableEq ι] (G : Matrix κ ι ℝ) :
    ForceClosure G.mulVecLin (orthantCone ι) ↔ PositivelySpans G.col := by
  have h : (fun i => G.mulVecLin (Pi.single i 1)) = G.col := by
    funext i
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  rw [forceClosure_orthantCone_iff_positivelySpans, h]

/-- MLS Proposition 5.3, (1) ⇔ (4), printed p. 226: a frictionless grasp with matrix
`G ∈ ℝ^{p×m}` is force-closure if and only if there is no `v ∈ ℝ^p`, `v ≠ 0`, with `v · Gᵢ ≥ 0`
for every column `Gᵢ` (no supporting hyperplane through the origin). MLS refers this to [97];
proved here by separation (Mathlib `geometric_hahn_banach_point_closed`) and the open mapping
property of surjective linear maps in finite dimension. Finite-force caveat: unbounded contact
forces, maintained rigid contacts (MLS p. 214). -/
theorem forceClosure_mulVecLin_iff_not_exists_dotProduct_nonneg [DecidableEq ι]
    (G : Matrix κ ι ℝ) :
    ForceClosure G.mulVecLin (orthantCone ι) ↔
      ¬ ∃ v : κ → ℝ, v ≠ 0 ∧ ∀ i, 0 ≤ v ⬝ᵥ G.col i := by
  classical
  set L := G.mulVecLin with hL
  set K : Set (κ → ℝ) := L '' (orthantCone ι : Set (ι → ℝ)) with hK
  constructor
  · rintro h ⟨v, hv, hpos⟩
    obtain ⟨f, hf, hGf⟩ := h v
    have h1 : 0 ≤ v ⬝ᵥ L f := by
      rw [hL, Matrix.mulVecLin_apply, mulVec_eq_sum_col, dotProduct_sum]
      exact Finset.sum_nonneg fun i _ => by
        rw [dotProduct_smul, smul_eq_mul]
        exact mul_nonneg (hf i) (hpos i)
    rw [hGf, dotProduct_neg] at h1
    have h2 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
    exact hv (dotProduct_self_eq_zero.mp (le_antisymm (by linarith) h2))
  · intro h4
    have hKconv : Convex ℝ K := (orthantCone ι).convex.linear_image L
    have h0K : (0 : κ → ℝ) ∈ K := ⟨0, fun _ => le_rfl, map_zero L⟩
    have hsmulK : ∀ b ∈ K, ∀ t : ℝ, 0 < t → t • b ∈ K := by
      rintro _ ⟨f, hf, rfl⟩ t ht
      exact ⟨t • f, fun i => mul_nonneg ht.le (hf i), map_smul L t f⟩
    -- the cone `K = G(FC)` is dense, by separation from a point outside its closure
    have hdense : Dense K := by
      rw [dense_iff_closure_eq]
      by_contra hne
      obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
      obtain ⟨φ, u, hφx, hφb⟩ := geometric_hahn_banach_point_closed hKconv.closure isClosed_closure hx
      have hu : u < 0 := by simpa using hφb 0 (subset_closure h0K)
      have hφK : ∀ b ∈ K, 0 ≤ φ b := by
        intro b hb
        refine le_of_not_gt fun hneg => ?_
        have hlt := hφb ((u / φ b) • b)
          (subset_closure (hsmulK b hb _ (div_pos_of_neg_of_neg hu hneg)))
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at hlt
        exact lt_irrefl _ hlt
      have hφ : ∀ z, φ z = (fun j => φ (Pi.single j 1)) ⬝ᵥ z := by
        intro z
        have hz := map_eq_sum_single (φ : (κ → ℝ) →ₗ[ℝ] ℝ) z
        simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at hz
        rw [hz, dotProduct]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      refine h4 ⟨fun j => φ (Pi.single j 1), ?_, fun i => ?_⟩
      · intro hy
        have hx0 := hφ x
        rw [hy, zero_dotProduct] at hx0
        linarith
      · rw [← hφ]
        exact hφK _ (col_mem_image_orthantCone G i)
    -- hence `G` is onto, and so an open map
    have hsurj : Function.Surjective L := by
      rw [← LinearMap.range_eq_top]
      have hcl : IsClosed (LinearMap.range L : Set (κ → ℝ)) :=
        Submodule.closed_of_finiteDimensional _
      have hsub : closure K ⊆ LinearMap.range L :=
        closure_minimal (by rintro _ ⟨f, -, rfl⟩; exact LinearMap.mem_range_self L f) hcl
      rw [hdense.closure_eq] at hsub
      exact eq_top_iff.mpr fun z _ => hsub (Set.mem_univ z)
    rw [forceClosure_iff_forall_exists]
    intro w
    set P : Set (ι → ℝ) := interior (orthantCone ι : Set (ι → ℝ))
    have hPo : IsOpen (L '' P) := L.isOpenMap_of_finiteDimensional hsurj _ isOpen_interior
    have hpre : IsOpen ((fun p => w - p) ⁻¹' (L '' P)) := hPo.preimage (continuous_const.sub continuous_id)
    have hne : ((fun p => w - p) ⁻¹' (L '' P)).Nonempty :=
      ⟨w - L (fun _ => 1), ⟨fun _ => 1, mem_interior_orthantCone fun _ => one_pos, by simp⟩⟩
    obtain ⟨p, ⟨g, hg, hgp⟩, ⟨f, hf, rfl⟩⟩ := hdense.inter_open_nonempty _ hpre hne
    refine ⟨f + g, fun i => add_nonneg (hf i) (interior_subset hg i), ?_⟩
    rw [map_add, show L g = w - L f from hgp, add_sub_cancel]

/-- MLS Proposition 5.3, (1) ⇔ (3), printed p. 226: a frictionless grasp with matrix
`G ∈ ℝ^{p×m}` and at least one column is force-closure if and only if the convex hull of the
columns contains a neighborhood of the origin. The hypothesis `[Nonempty ι]` (at least one
contact) is not stated in MLS; without it the equivalence fails for `p = 0`. MLS refers this
to [97]. Finite-force caveat: unbounded contact forces, maintained rigid contacts
(MLS p. 214). -/
theorem forceClosure_mulVecLin_iff_convexHull_mem_nhds [DecidableEq ι] [Nonempty ι]
    (G : Matrix κ ι ℝ) :
    ForceClosure G.mulVecLin (orthantCone ι) ↔
      convexHull ℝ (Set.range G.col) ∈ nhds (0 : κ → ℝ) := by
  classical
  set L := G.mulVecLin with hL
  set H := convexHull ℝ (Set.range G.col) with hH
  constructor
  · intro h
    have hsurj : Function.Surjective L := h.surjective
    obtain ⟨a, ha, ha0⟩ := (forceClosure_mulVecLin_iff_positivelySpans G).mp h 0
    have hS : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
    -- the origin is a convex combination of the columns
    have h0 : (0 : κ → ℝ) ∈ H := by
      have hm := (convex_convexHull ℝ (Set.range G.col)).sum_mem (t := Finset.univ)
        (w := fun i => (∑ j, a j)⁻¹ * a i) (z := G.col)
        (fun i _ => mul_nonneg (inv_nonneg.mpr hS.le) (ha i).le)
        (by rw [← Finset.mul_sum, inv_mul_cancel₀ hS.ne'])
        (fun i _ => subset_convexHull ℝ _ (Set.mem_range_self i))
      have heq : ∑ i, ((∑ j, a j)⁻¹ * a i) • G.col i = 0 := by
        simp_rw [mul_smul]
        rw [← Finset.smul_sum, ha0, smul_zero]
      rwa [heq] at hm
    -- the image under `G` of an open set of positive coefficients with sum below one
    set U : Set (ι → ℝ) := {α | ∀ i, 0 < α i} ∩ {α | ∑ i, α i < 1}
    have hUo : IsOpen U := by
      refine IsOpen.inter ?_
        (isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
      simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
    have hcU : (2 * ∑ i, a i)⁻¹ • a ∈ U := by
      refine ⟨fun i => ?_, ?_⟩
      · exact mul_pos (inv_pos.mpr (by linarith)) (ha i)
      · change ∑ i, (2 * ∑ j, a j)⁻¹ * a i < 1
        rw [← Finset.mul_sum, mul_inv, mul_assoc, inv_mul_cancel₀ hS.ne']
        norm_num
    have hLc : L ((2 * ∑ i, a i)⁻¹ • a) = 0 := by
      rw [map_smul, hL, Matrix.mulVecLin_apply, mulVec_eq_sum_col, ha0, smul_zero]
    have hnhds := (L.isOpenMap_of_finiteDimensional hsurj).image_mem_nhds (hUo.mem_nhds hcU)
    rw [hLc] at hnhds
    refine Filter.mem_of_superset hnhds ?_
    rintro _ ⟨α, ⟨hαpos, hαlt⟩, rfl⟩
    have hs : 0 < ∑ i, α i := Finset.sum_pos (fun i _ => hαpos i) Finset.univ_nonempty
    have hz := (convex_convexHull ℝ (Set.range G.col)).sum_mem (t := Finset.univ)
      (w := fun i => (∑ j, α j)⁻¹ * α i) (z := G.col)
      (fun i _ => mul_nonneg (inv_nonneg.mpr hs.le) (hαpos i).le)
      (by rw [← Finset.mul_sum, inv_mul_cancel₀ hs.ne'])
      (fun i _ => subset_convexHull ℝ _ (Set.mem_range_self i))
    have hm := (convex_convexHull ℝ (Set.range G.col)).smul_mem_of_zero_mem h0 hz
      ⟨hs.le, (show ∑ i, α i < 1 from hαlt).le⟩
    have heq : (∑ i, α i) • ∑ i, ((∑ j, α j)⁻¹ * α i) • G.col i = ∑ i, α i • G.col i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
    rw [heq] at hm
    rw [hL, Matrix.mulVecLin_apply, mulVec_eq_sum_col]
    exact hm
  · intro h3
    rw [forceClosure_iff_forall_exists]
    intro x
    have hsub : H ⊆ L '' (orthantCone ι : Set (ι → ℝ)) :=
      convexHull_min (by rintro _ ⟨i, rfl⟩; exact col_mem_image_orthantCone G i)
        ((orthantCone ι).convex.linear_image L)
    -- a small positive multiple of `x` lies in the hull
    have hcont : Continuous fun t : ℝ => t • x := continuous_id.smul continuous_const
    have hpre : (fun t : ℝ => t • x) ⁻¹' H ∈ nhds (0 : ℝ) :=
      hcont.continuousAt.preimage_mem_nhds (by simpa using h3)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
    have ht : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
      linarith
    obtain ⟨f, hf, hLf⟩ := hsub (hball ht)
    refine ⟨(ε / 2)⁻¹ • f, fun i => mul_nonneg (inv_nonneg.mpr (by positivity)) (hf i), ?_⟩
    rw [map_smul, hLf, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

/-- **MLS Proposition 5.3**, printed p. 226 (convexity conditions for force-closure grasps): for
a fixed grasp of frictionless point contacts with matrix `G ∈ ℝ^{p×m}` (at least one column), the
four conditions — (1) force-closure, (2) the columns positively span `ℝ^p`, (3) their convex hull
contains a neighborhood of `0`, (4) no `v ≠ 0` has `v · Gᵢ ≥ 0` for all columns — are equivalent.
Finite-force caveat: unbounded contact forces, maintained rigid contacts (MLS p. 214). -/
theorem frictionless_tfae [DecidableEq ι] [Nonempty ι] (G : Matrix κ ι ℝ) :
    List.TFAE
      [ForceClosure G.mulVecLin (orthantCone ι),
        PositivelySpans G.col,
        convexHull ℝ (Set.range G.col) ∈ nhds (0 : κ → ℝ),
        ¬ ∃ v : κ → ℝ, v ≠ 0 ∧ ∀ i, 0 ≤ v ⬝ᵥ G.col i] := by
  tfae_have 1 ↔ 2 := forceClosure_mulVecLin_iff_positivelySpans G
  tfae_have 1 ↔ 3 := forceClosure_mulVecLin_iff_convexHull_mem_nhds G
  tfae_have 1 ↔ 4 := forceClosure_mulVecLin_iff_not_exists_dotProduct_nonneg G
  tfae_finish

/-! ### Cones generated by finitely many edges (Example 5.5) -/

/-- Force-closure over a cone given as the image `L(S)` of a set of generator coefficients is
force-closure of `G ∘ L` over `S` (MLS Example 5.5, printed p. 228: "by appropriate choice of
basis, we can use Proposition 5.3"; with `S` the orthant and `L` the edge generators of each
friction cone). Finite-force caveat: unbounded contact forces, maintained rigid contacts
(MLS p. 214). -/
theorem forceClosure_image_iff {E E' : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup E']
    [Module ℝ E'] (G : E →ₗ[ℝ] W) (L : E' →ₗ[ℝ] E) (S : Set E') :
    ForceClosure G (L '' S) ↔ ForceClosure (G ∘ₗ L) S := by
  constructor
  · intro h Fe
    obtain ⟨_, ⟨s, hs, rfl⟩, hG⟩ := h Fe
    exact ⟨s, hs, hG⟩
  · intro h Fe
    obtain ⟨s, hs, hG⟩ := h Fe
    exact ⟨L s, ⟨s, hs, rfl⟩, hG⟩

/-- MLS Example 5.5, printed p. 228: every force in the planar friction cone
`|f₁| ≤ μ f₂, f₂ ≥ 0` (Example 5.3, p. 222) is a nonnegative combination of the two edge forces
`(μ, 1)` and `(-μ, 1)` of the cone, and conversely, for `μ > 0`. -/
theorem mem_planarPointContactCone_iff_edges {μ : ℝ} (hμ : 0 < μ) {f : Fin 2 → ℝ} :
    f ∈ planarPointContactCone μ ↔
      ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ f = s • ![μ, 1] + t • ![-μ, 1] := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨(f 1 + f 0 / μ) / 2, (f 1 - f 0 / μ) / 2, ?_, ?_, ?_⟩
    · have : -(μ * f 1) ≤ f 0 := (abs_le.mp h₁).1
      have : -f 1 ≤ f 0 / μ := by rw [le_div_iff₀ hμ]; linarith
      linarith
    · have : f 0 ≤ μ * f 1 := (abs_le.mp h₁).2
      have : f 0 / μ ≤ f 1 := by rw [div_le_iff₀ hμ]; linarith
      linarith
    · funext i
      fin_cases i <;> simp <;> field_simp <;> ring
  · rintro ⟨s, t, hs, ht, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [abs_le]
      constructor <;> nlinarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      linarith

/-! ### Spatial grasps of frictionless point contacts (p. 224) -/

/-- The frictionless contact force space `(i : ι) → ℝ¹` of a contact grasp is `ι → ℝ` (supporting
declaration for MLS printed p. 224, `FC = {f ∈ ℝ^k : fᵢ ≥ 0}`). -/
def frictionlessCoefficients : (ι → ℝ) →ₗ[ℝ] ((i : ι) → Fin 1 → ℝ) where
  toFun f i _ := f i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **MLS printed p. 224** (with Example 5.1, p. 220): a fixed grasp of `k` frictionless point
contacts with frames `g_{ocᵢ} = (p_{cᵢ}, R_{cᵢ})` is force-closure if and only if the columns
`(n_{cᵢ}; p_{cᵢ} × n_{cᵢ})` of its grasp map, `n_{cᵢ} = R_{cᵢ} e_z`, positively span the wrench space
("`G(FC) = ℝ⁶` if and only if positive linear combinations of the columns of `G` span `ℝ⁶`").
Finite-force caveat: unbounded contact forces at maintained rigid contacts (MLS p. 214). -/
theorem spatial_frictionless_isForceClosure_iff [DecidableEq ι] (frame : ι → RigidTransform) :
    (ContactGrasp.spatial (fun _ => ContactModel.frictionless) frame).toGrasp.IsForceClosure ↔
      PositivelySpans fun i =>
        Wrench.pointForce (frame i).translation ((frame i).rotation.act Rotation.zAxis) := by
  set g := ContactGrasp.spatial (fun _ : ι => ContactModel.frictionless) frame
  have hcone : (g.cone : Set ((i : ι) → Fin 1 → ℝ)) =
      frictionlessCoefficients '' (orthantCone ι : Set (ι → ℝ)) := by
    ext f
    constructor
    · intro hf
      refine ⟨fun i => f i 0, fun i => ?_, ?_⟩
      · exact FrictionCone.mem_frictionless.mp ((ContactGrasp.mem_cone g).mp hf i)
      · funext i j
        rw [Subsingleton.elim j 0]
        rfl
    · rintro ⟨f, hf, rfl⟩
      exact (ContactGrasp.mem_cone g).mpr fun i => FrictionCone.mem_frictionless.mpr (hf i)
  change ForceClosure g.graspMap (g.cone : Set ((i : ι) → Fin 1 → ℝ)) ↔ _
  rw [hcone, forceClosure_image_iff, forceClosure_orthantCone_iff_positivelySpans]
  have hcol : (fun i => (g.graspMap ∘ₗ frictionlessCoefficients) (Pi.single i 1)) =
      fun i => Wrench.pointForce (frame i).translation ((frame i).rotation.act Rotation.zAxis) := by
    funext i
    rw [LinearMap.comp_apply, ContactGrasp.spatial_frictionless_graspMap,
      Finset.sum_eq_single i]
    · simp [frictionlessCoefficients]
    · intro j _ hj
      simp [frictionlessCoefficients, Pi.single_eq_of_ne hj]
    · simp
  rw [hcol]

end Grasp
end RoboLean
