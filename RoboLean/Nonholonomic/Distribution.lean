import RoboLean.Nonholonomic.VectorField
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Distributions spanned by vector fields (MLS Chapter 7, §2.2)

MLS Chapter 7, printed pp. 325–326: a distribution assigns a subspace of the tangent space to each
point; for vector fields `g₁, …, g_m` it is `Δ = span{g₁, …, g_m}` and at a point
`Δ_q = span{g₁(q), …, g_m(q)}`; "regular" means that the dimension of `Δ_q` does not vary with
`q`; "involutive" means `∀ f, g ∈ Δ, [f, g] ∈ Δ`, and "for a finite dimensional distribution it
suffices to check that the Lie brackets of the basis elements are contained in the distribution".
Exercise 8 (p. 351): a one-dimensional distribution is involutive.

**Conventions.** A distribution is a pointwise assignment `D : E → Submodule ℝ E`; the
distribution spanned by a set `S` of fields is `spanAt S q`, the real span of the values `f q`,
`f ∈ S` (MLS's `Δ_q`). The book takes the span "over the set of smooth real-valued functions";
pointwise values of such combinations are real combinations of the values, so `spanAt` is the
book's `Δ_q`. `IsInvolutiveOn D U` is the book's definition read with sections: for all fields
`f, g` differentiable on `U` with values in `D` on `U`, `[f, g](q) ∈ D q` for `q ∈ U`.
`GeneratorsInvolutiveOn S U` is the book's criterion on generators. Every section-involutive
spanned distribution satisfies the criterion (`IsInvolutiveOn.generatorsInvolutiveOn`), and the
criterion gives the bracket of any two combinations of the generators with coefficients
differentiable at `q` (`GeneratorsInvolutiveOn.lieBracket_mem`). That the criterion implies section
involutivity for every differentiable section of a regular distribution needs local frames and is
not formalized here.
-/

noncomputable section

open Set Filter Topology VectorField

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **MLS p. 325: the distribution spanned by a set `S` of vector fields, at the point `q`:**
`Δ_q = span{f(q) : f ∈ S}`, the real span of the values of the fields of `S` at `q`. -/
def spanAt (S : Set (E → E)) (q : E) : Submodule ℝ E :=
  Submodule.span ℝ ((fun f : E → E => f q) '' S)

/-- **MLS p. 325:** the value of a generating field lies in `Δ_q`. -/
theorem mem_spanAt {S : Set (E → E)} {f : E → E} (hf : f ∈ S) (q : E) : f q ∈ spanAt S q := by
  exact Submodule.subset_span ⟨f, hf, rfl⟩

/-- **MLS p. 325:** more fields span a larger subspace at every point. -/
theorem spanAt_mono {S T : Set (E → E)} (h : S ⊆ T) (q : E) : spanAt S q ≤ spanAt T q := by
  exact Submodule.span_mono (Set.image_mono h)

/-- **MLS p. 325: `Δ_q = span{g₁(q), …, g_m(q)}`** for a family of generators. -/
theorem spanAt_range {ι : Type*} (g : ι → E → E) (q : E) :
    spanAt (Set.range g) q = Submodule.span ℝ (Set.range fun j => g j q) := by
  rw [spanAt, ← Set.range_comp]
  rfl

/-- **MLS p. 325:** a combination `Σ αⱼ(q) gⱼ(q)` of the generators lies in `Δ_q`. -/
theorem sum_smul_mem_spanAt {ι : Type*} [Fintype ι] (g : ι → E → E) (α : ι → E → ℝ) (q : E) :
    ∑ j, α j q • g j q ∈ spanAt (Set.range g) q := by
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mem_spanAt (Set.mem_range_self j) q)

/-- **MLS p. 325: a regular distribution on `U`:** the dimension of `D q` is the same at every
`q ∈ U`. -/
def IsRegularOn (D : E → Submodule ℝ E) (U : Set E) : Prop :=
  ∃ r : ℕ, ∀ q ∈ U, Module.finrank ℝ (D q) = r

/-- **MLS p. 325: an involutive distribution on `U`, "∀ f, g ∈ Δ, [f, g] ∈ Δ",** read with
sections: for all fields `f, g` differentiable at every point of `U` with `f q, g q ∈ D q` for
`q ∈ U`, the bracket satisfies `[f, g](q) ∈ D q` for `q ∈ U`. -/
def IsInvolutiveOn (D : E → Submodule ℝ E) (U : Set E) : Prop :=
  ∀ f g : E → E, (∀ q ∈ U, DifferentiableAt ℝ f q) → (∀ q ∈ U, DifferentiableAt ℝ g q) →
    (∀ q ∈ U, f q ∈ D q) → (∀ q ∈ U, g q ∈ D q) → ∀ q ∈ U, lieBracket ℝ f g q ∈ D q

/-- **MLS p. 325: "it suffices to check that the Lie brackets of the basis elements are contained
in the distribution":** the brackets of any two generators of `S` lie in `Δ_q` at every `q ∈ U`. -/
def GeneratorsInvolutiveOn (S : Set (E → E)) (U : Set E) : Prop :=
  ∀ q ∈ U, ∀ f ∈ S, ∀ g ∈ S, lieBracket ℝ f g q ∈ spanAt S q

/-- **MLS p. 325:** a section-involutive spanned distribution satisfies the generator criterion,
when the generators are differentiable on `U`. -/
theorem IsInvolutiveOn.generatorsInvolutiveOn {S : Set (E → E)} {U : Set E}
    (h : IsInvolutiveOn (spanAt S) U) (hS : ∀ f ∈ S, ∀ q ∈ U, DifferentiableAt ℝ f q) :
    GeneratorsInvolutiveOn S U := by
  intro q hq f hf g hg
  exact h f g (hS f hf) (hS g hg) (fun x _ => mem_spanAt hf x) (fun x _ => mem_spanAt hg x) q hq

/-- The bracket is additive over a finite sum in its first argument (MLS Proposition 7.1, p. 325):
`[Σ Fₐ, W](q) = Σ [Fₐ, W](q)` for fields `Fₐ` differentiable at `q`. -/
private theorem lieBracket_sum_left {ι : Type*} [Fintype ι] {F : ι → E → E} {q : E}
    (hF : ∀ a, DifferentiableAt ℝ (F a) q) (W : E → E) :
    lieBracket ℝ (fun x => ∑ a, F a x) W q = ∑ a, lieBracket ℝ (F a) W q := by
  simp only [lieBracket]
  rw [fderiv_fun_sum (fun a _ => hF a), map_sum, sum_apply,
    Finset.sum_sub_distrib]

/-- The bracket is additive over a finite sum in its second argument (MLS Proposition 7.1, p. 325):
`[V, Σ G_b](q) = Σ [V, G_b](q)` for fields `G_b` differentiable at `q`. -/
private theorem lieBracket_sum_right {κ : Type*} [Fintype κ] {G : κ → E → E} {q : E}
    (hG : ∀ b, DifferentiableAt ℝ (G b) q) (V : E → E) :
    lieBracket ℝ V (fun x => ∑ b, G b x) q = ∑ b, lieBracket ℝ V (G b) q := by
  simp only [lieBracket]
  rw [fderiv_fun_sum (fun b _ => hG b), map_sum, sum_apply,
    Finset.sum_sub_distrib]

/-- **MLS Proposition 7.1 (3), p. 325, for finite combinations:** for families `u, v` of fields
and coefficients `α, β`, all differentiable at `q`,
`[Σ αₐ uₐ, Σ β_b v_b](q) = Σ αₐ β_b [uₐ, v_b](q) + Σ αₐ (L_{uₐ} β_b) v_b(q) − Σ β_b (L_{v_b} αₐ) uₐ(q)`.
-/
theorem lieBracket_sum_smul_sum_smul {ι κ : Type*} [Fintype ι] [Fintype κ] {u : ι → E → E}
    {v : κ → E → E} {α : ι → E → ℝ} {β : κ → E → ℝ} {q : E}
    (hu : ∀ a, DifferentiableAt ℝ (u a) q) (hv : ∀ b, DifferentiableAt ℝ (v b) q)
    (hα : ∀ a, DifferentiableAt ℝ (α a) q) (hβ : ∀ b, DifferentiableAt ℝ (β b) q) :
    lieBracket ℝ (fun x => ∑ a, α a x • u a x) (fun x => ∑ b, β b x • v b x) q =
      ∑ a, ∑ b, (α a q * β b q) • lieBracket ℝ (u a) (v b) q +
        ∑ a, ∑ b, (α a q * lieDerivative (u a) (β b) q) • v b q -
          ∑ a, ∑ b, (β b q * lieDerivative (v b) (α a) q) • u a q := by
  rw [lieBracket_sum_left (F := fun a x => α a x • u a x) (fun a => (hα a).smul (hu a))]
  simp_rw [lieBracket_sum_right (G := fun b x => β b x • v b x) (fun b => (hβ b).smul (hv b)),
    lieBracket_smul_smul (hα _) (hβ _) (hu _) (hv _)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- **MLS p. 325: the generator criterion suffices.** If the brackets of the generators `g` lie in
`Δ_q` at `q ∈ U`, then for fields `f, h` equal near `q` to combinations `Σ αⱼ gⱼ`, `Σ βⱼ gⱼ` with
coefficients differentiable at `q` (generators differentiable at `q`), `[f, h](q) ∈ Δ_q`. -/
theorem GeneratorsInvolutiveOn.lieBracket_mem {ι : Type*} [Fintype ι] {g : ι → E → E}
    {U : Set E} {q : E} (h : GeneratorsInvolutiveOn (Set.range g) U) (hq : q ∈ U)
    (hg : ∀ j, DifferentiableAt ℝ (g j) q) {f k : E → E} {α β : ι → E → ℝ}
    (hα : ∀ j, DifferentiableAt ℝ (α j) q) (hβ : ∀ j, DifferentiableAt ℝ (β j) q)
    (hf : f =ᶠ[𝓝 q] fun x => ∑ j, α j x • g j x) (hk : k =ᶠ[𝓝 q] fun x => ∑ j, β j x • g j x) :
    lieBracket ℝ f k q ∈ spanAt (Set.range g) q := by
  rw [hf.lieBracket_vectorField_eq hk, lieBracket_sum_smul_sum_smul hg hg hα hβ]
  refine Submodule.sub_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ ?_
  · exact h q hq _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  · exact mem_spanAt (Set.mem_range_self b) q
  · exact mem_spanAt (Set.mem_range_self a) q

/-- **MLS Exercise 8, p. 351, the formula:** for a field `f` and functions `α, β`, all
differentiable at `q`, `[α f, β f](q) = (α (L_f β) − β (L_f α))(q) f(q)`. -/
theorem lieBracket_smul_smul_self {f : E → E} {α β : E → ℝ} {q : E}
    (hα : DifferentiableAt ℝ α q) (hβ : DifferentiableAt ℝ β q) (hf : DifferentiableAt ℝ f q) :
    lieBracket ℝ (fun x => α x • f x) (fun x => β x • f x) q =
      (α q * lieDerivative f β q - β q * lieDerivative f α q) • f q := by
  rw [lieBracket_smul_smul hα hβ hf hf, lieBracket_self, Pi.zero_apply, smul_zero, zero_add,
    sub_smul]

/-- **MLS Exercise 8, p. 351: a one-dimensional distribution `Δ_q = span{f(q)}` is involutive:**
`[α f, β f](q) ∈ span{f(q)}` for `α, β, f` differentiable at `q`. -/
theorem lieBracket_smul_smul_self_mem {f : E → E} {α β : E → ℝ} {q : E}
    (hα : DifferentiableAt ℝ α q) (hβ : DifferentiableAt ℝ β q) (hf : DifferentiableAt ℝ f q) :
    lieBracket ℝ (fun x => α x • f x) (fun x => β x • f x) q ∈ spanAt {f} q := by
  rw [lieBracket_smul_smul_self hα hβ hf]
  exact Submodule.smul_mem _ _ (mem_spanAt (Set.mem_singleton f) q)

/-- **MLS Exercise 8, p. 351, generator form:** a single field satisfies the generator criterion
everywhere. -/
theorem generatorsInvolutiveOn_singleton (f : E → E) (U : Set E) :
    GeneratorsInvolutiveOn {f} U := by
  intro q _ f₁ hf₁ f₂ hf₂
  rw [Set.mem_singleton_iff] at hf₁ hf₂
  rw [hf₁, hf₂, lieBracket_self]
  exact zero_mem _

end Nonholonomic
end RoboLean
