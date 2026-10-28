import RoboLean.Nonholonomic.Filtration

/-!
# Brackets along the filtration: MLS Exercises 10 and 11 of Chapter 7

MLS Chapter 7, printed p. 340 and Exercises 10–11, p. 351: "The Jacobi identity implies that
`[Δᵢ, Δⱼ] ⊂ [Δ₁, Δᵢ₊ⱼ₋₁] ⊂ Δᵢ₊ⱼ`" (Exercise 10), and "Let `Δᵢ, i = 1, …, κ` be a regular filtration
associated with a distribution. Show that if `rank(Δᵢ₊₁) = rank(Δᵢ)` then `Δᵢ` is involutive"
(Exercise 11; p. 340 adds "and hence `Δᵢ₊ⱼ = Δᵢ` for all `j ≥ 0`").

**Conventions.** The book's distributions are spans "over the set of smooth real-valued
functions" (p. 325): `InSmoothSpan S f` says that `f` is a finite sum `Σ cₖ wₖ` with `wₖ ∈ S` and
smooth coefficients `cₖ : E → ℝ`. The generators are smooth (`ContDiff ℝ ∞`, MLS: smooth).

**Formalized.** Exercise 10, outer inclusion: for `f` spanning `Δᵢ` and `h` spanning `Δⱼ`, the
bracket `[f, h]` lies in the smooth span of the fields spanning `Δᵢ₊ⱼ`, hence `[f, h](q) ∈ Δᵢ₊ⱼ(q)`
at every point; the middle term `[Δ₁, Δᵢ₊ⱼ₋₁]` is not stated separately. Exercise 11 is proved
under the hypothesis that every field spanning `Δᵢ₊₁` lies in the smooth span of the fields spanning
`Δᵢ` (the module form of `Δᵢ₊₁ = Δᵢ`); this hypothesis implies `rank Δᵢ₊₁(q) = rank Δᵢ(q)` at every
point. The book's route from equal ranks of a regular filtration to this inclusion uses local frames
of constant-rank distributions and is not formalized here.
-/

noncomputable section

open Set Filter Topology VectorField
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- **MLS p. 325: the span of a set `S` of fields "over the set of smooth real-valued
functions":** `f` is a finite sum `Σ cₖ wₖ` with `wₖ ∈ S` and smooth `cₖ`. -/
inductive InSmoothSpan (S : Set (E → E)) : (E → E) → Prop
  /-- The zero field. -/
  | zero : InSmoothSpan S 0
  /-- Adding a smooth multiple of a field of `S`. -/
  | add_smul {f w : E → E} {c : E → ℝ} : InSmoothSpan S f → w ∈ S → ContDiff ℝ ∞ c →
      InSmoothSpan S (fun x => f x + c x • w x)

/-- **MLS p. 325:** the value at `q` of a field in the smooth span of `S` lies in `Δ_q`. -/
theorem InSmoothSpan.mem_spanAt {S : Set (E → E)} {f : E → E} (h : InSmoothSpan S f) (q : E) :
    f q ∈ spanAt S q := by
  induction h with
  | zero => exact Submodule.zero_mem _
  | add_smul _ hw _ ih =>
    exact Submodule.add_mem _ ih
      (Submodule.smul_mem _ _ (_root_.RoboLean.Nonholonomic.mem_spanAt hw q))

/-- **MLS p. 325:** a field of `S` lies in its smooth span. -/
theorem InSmoothSpan.of_mem {S : Set (E → E)} {w : E → E} (hw : w ∈ S) : InSmoothSpan S w := by
  have h := InSmoothSpan.add_smul (c := fun _ => (1 : ℝ)) (InSmoothSpan.zero (S := S)) hw
    contDiff_const
  convert h using 1
  funext x
  simp

/-- **MLS p. 325:** the smooth span grows with the set of fields. -/
theorem InSmoothSpan.mono {S T : Set (E → E)} (hST : S ⊆ T) {f : E → E} (h : InSmoothSpan S f) :
    InSmoothSpan T f := by
  induction h with
  | zero => exact InSmoothSpan.zero
  | add_smul _ hw hc ih => exact ih.add_smul (hST hw) hc

/-- **MLS p. 325:** the smooth span is closed under sums. -/
theorem InSmoothSpan.add {S : Set (E → E)} {f h : E → E} (hf : InSmoothSpan S f)
    (hh : InSmoothSpan S h) : InSmoothSpan S (f + h) := by
  induction hh with
  | zero => simpa using hf
  | @add_smul h' w c _ hw hc ih =>
    convert ih.add_smul hw hc using 1
    funext x
    simp [add_assoc]

/-- **MLS p. 325:** the smooth span is closed under multiplication by smooth functions. -/
theorem InSmoothSpan.smul {S : Set (E → E)} {c : E → ℝ} (hc : ContDiff ℝ ∞ c) {f : E → E}
    (hf : InSmoothSpan S f) : InSmoothSpan S (fun x => c x • f x) := by
  induction hf with
  | zero =>
    convert (InSmoothSpan.zero (S := S)) using 1
    funext x
    simp
  | @add_smul f' w c' _ hw hc' ih =>
    convert ih.add_smul hw (hc.mul hc') using 1
    funext x
    simp [smul_add, smul_smul]

/-- **MLS p. 325:** the smooth span is closed under differences. -/
theorem InSmoothSpan.sub {S : Set (E → E)} {f h : E → E} (hf : InSmoothSpan S f)
    (hh : InSmoothSpan S h) : InSmoothSpan S (f - h) := by
  have h := hf.add (hh.smul (c := fun _ => (-1 : ℝ)) contDiff_const)
  convert h using 1
  funext x
  simp [sub_eq_add_neg]

/-- **MLS p. 325:** if every field of `T` lies in the smooth span of `S`, so does every field of
the smooth span of `T`. -/
theorem InSmoothSpan.trans {S T : Set (E → E)} (hT : ∀ w ∈ T, InSmoothSpan S w) {f : E → E}
    (h : InSmoothSpan T f) : InSmoothSpan S f := by
  induction h with
  | zero => exact InSmoothSpan.zero
  | add_smul _ hw hc ih => exact ih.add ((hT _ hw).smul hc)

/-- **MLS p. 325:** the smooth span of smooth fields consists of smooth fields. -/
theorem InSmoothSpan.contDiff {S : Set (E → E)} (hS : ∀ w ∈ S, ContDiff ℝ ∞ w) {f : E → E}
    (h : InSmoothSpan S f) : ContDiff ℝ ∞ f := by
  induction h with
  | zero => exact contDiff_const
  | add_smul _ hw hc ih => exact ih.add (hc.smul (hS _ hw))

/-- **MLS Proposition 7.1 (3), p. 325, in module form:** for smooth `g` and smooth fields `S`, the
bracket `[g, f]` of a field `f` in the smooth span of `S` lies in the smooth span of `S` together
with the brackets `[g, w]`, `w ∈ S`. -/
theorem InSmoothSpan.lieBracket_left {S : Set (E → E)} {g : E → E} (hg : ContDiff ℝ ∞ g)
    (hS : ∀ w ∈ S, ContDiff ℝ ∞ w) {f : E → E} (h : InSmoothSpan S f) :
    InSmoothSpan (S ∪ {k | ∃ w ∈ S, k = lieBracket ℝ g w}) (lieBracket ℝ g f) := by
  have hd : ∀ {k : E → E}, ContDiff ℝ ∞ k → Differentiable ℝ k :=
    fun hk => hk.differentiable (by simp)
  induction h with
  | zero =>
    rw [lieBracket_zero_right]
    exact InSmoothSpan.zero
  | @add_smul f w c hf hw hc ih =>
    have hf' : ContDiff ℝ ∞ f := hf.contDiff hS
    have hdc : Differentiable ℝ c := hc.differentiable (by simp)
    have hLc : ContDiff ℝ ∞ (fun x => fderiv ℝ c x (g x)) :=
      (hc.fderiv_right (m := ∞) (by simp)).clm_apply hg
    have key : lieBracket ℝ g (fun x => f x + c x • w x) =
        lieBracket ℝ g f + ((fun x => fderiv ℝ c x (g x) • w x) +
          fun x => c x • lieBracket ℝ g w x) := by
      funext x
      have e : (fun x => f x + c x • w x) = f + fun x => c x • w x := rfl
      rw [e, lieBracket_add_right (W₁ := fun y => c y • w y) (hd hf' x)
          ((hdc x).smul (hd (hS w hw) x)),
        lieBracket_smul_right (hdc x) (hd (hS w hw) x)]
      simp
    rw [key]
    have hgw : lieBracket ℝ g w ∈ {k | ∃ w ∈ S, k = lieBracket ℝ g w} := ⟨w, hw, rfl⟩
    exact ih.add (((InSmoothSpan.of_mem (mem_union_left _ hw)).smul hLc).add
      ((InSmoothSpan.of_mem (mem_union_right _ hgw)).smul hc))

/-- **MLS p. 340:** for smooth generators, every field spanning a level of the filtration is
smooth. -/
theorem contDiff_of_mem_filtrationFields {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    {i : ℕ} {f : E → E} (hf : f ∈ filtrationFields g i) : ContDiff ℝ ∞ f := by
  induction i generalizing f with
  | zero => simp [filtrationFields] at hf
  | succ i ih =>
    simp only [filtrationFields, mem_union, mem_range, mem_ofPred_eq] at hf
    rcases hf with ⟨j, rfl⟩ | ⟨j, w, hw, rfl⟩
    · exact hg j
    · exact (hg j).lieBracket_vectorField (ih hw) (by simp)

/-- **MLS Exercise 10, p. 351 (and p. 340): `[Δᵢ, Δⱼ] ⊂ Δᵢ₊ⱼ`,** in the module form: for smooth
generators, the bracket of a field spanning `Δᵢ` with a field spanning `Δⱼ` is a smooth combination
of the fields spanning `Δᵢ₊ⱼ`. -/
theorem lieBracket_inSmoothSpan_filtrationFields {g : Fin m → E → E}
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) {i j : ℕ} {f h : E → E} (hf : f ∈ filtrationFields g i)
    (hh : h ∈ filtrationFields g j) :
    InSmoothSpan (filtrationFields g (i + j)) (lieBracket ℝ f h) := by
  have hS : ∀ k, ∀ w ∈ filtrationFields g k, ContDiff ℝ ∞ w :=
    fun k w hw => contDiff_of_mem_filtrationFields hg hw
  have hn : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by simp
  induction i generalizing j f h with
  | zero => simp [filtrationFields] at hf
  | succ i ih =>
    rw [show i + 1 + j = i + j + 1 by omega]
    simp only [filtrationFields, mem_union, mem_range, mem_ofPred_eq] at hf
    rcases hf with ⟨a, rfl⟩ | ⟨a, f', hf', rfl⟩
    · refine InSmoothSpan.of_mem ?_
      exact filtrationFields_mono g (by omega) (lieBracket_mem_filtrationFields g a hh)
    · have key : lieBracket ℝ (lieBracket ℝ (g a) f') h =
          lieBracket ℝ (g a) (lieBracket ℝ f' h) - lieBracket ℝ f' (lieBracket ℝ (g a) h) := by
        funext x
        rw [Pi.sub_apply, leibniz_identity_lieBracket hn (hg a).contDiffAt
          (hS _ _ hf').contDiffAt (hS _ _ hh).contDiffAt]
        abel
      rw [key]
      refine InSmoothSpan.sub ?_ ?_
      · refine ((ih hf' hh).lieBracket_left (hg a) (hS _)).mono ?_
        rintro k (hk | ⟨w, hw, rfl⟩)
        · exact filtrationFields_mono g (by omega) hk
        · exact lieBracket_mem_filtrationFields g a hw
      · have h2 := ih hf' (lieBracket_mem_filtrationFields g a hh)
        rwa [show i + (j + 1) = i + j + 1 by omega] at h2

/-- **MLS Exercise 10, p. 351, at a point: `[f, h](q) ∈ Δᵢ₊ⱼ(q)`** for `f` spanning `Δᵢ` and `h`
spanning `Δⱼ`, smooth generators. -/
theorem lieBracket_mem_filtrationAt {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    {i j : ℕ} {f h : E → E} (hf : f ∈ filtrationFields g i) (hh : h ∈ filtrationFields g j)
    (q : E) : lieBracket ℝ f h q ∈ filtrationAt g (i + j) q := by
  exact (lieBracket_inSmoothSpan_filtrationFields hg hf hh).mem_spanAt q

/-- **MLS p. 340, "and hence `Δᵢ₊ⱼ = Δᵢ` for all `j ≥ 0`", in module form:** if every field
spanning `Δᵢ₊₁` is a smooth combination of the fields spanning `Δᵢ`, then so is every field spanning
`Δᵢ₊ⱼ`, for smooth generators. -/
theorem inSmoothSpan_of_mem_filtrationFields_add {g : Fin m → E → E}
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) {i : ℕ}
    (hstep : ∀ w ∈ filtrationFields g (i + 1), InSmoothSpan (filtrationFields g i) w) (j : ℕ)
    {w : E → E} (hw : w ∈ filtrationFields g (i + j)) :
    InSmoothSpan (filtrationFields g i) w := by
  have hS : ∀ w ∈ filtrationFields g i, ContDiff ℝ ∞ w :=
    fun w hw => contDiff_of_mem_filtrationFields hg hw
  induction j generalizing w with
  | zero => exact InSmoothSpan.of_mem hw
  | succ j ih =>
    rw [← Nat.add_assoc] at hw
    simp only [filtrationFields, mem_union, mem_range, mem_ofPred_eq] at hw
    rcases hw with ⟨a, rfl⟩ | ⟨a, w', hw', rfl⟩
    · refine hstep _ ?_
      simp only [filtrationFields, mem_union, mem_range]
      exact Or.inl ⟨a, rfl⟩
    · refine InSmoothSpan.trans ?_ ((ih hw').lieBracket_left (hg a) hS)
      rintro k (hk | ⟨v, hv, rfl⟩)
      · exact InSmoothSpan.of_mem hk
      · exact hstep _ (lieBracket_mem_filtrationFields g a hv)

/-- **MLS p. 340, "`Δᵢ₊ⱼ = Δᵢ` for all `j ≥ 0`", at a point,** under the module form of
`Δᵢ₊₁ = Δᵢ`, smooth generators. -/
theorem filtrationAt_add_eq {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j)) {i : ℕ}
    (hstep : ∀ w ∈ filtrationFields g (i + 1), InSmoothSpan (filtrationFields g i) w) (j : ℕ)
    (q : E) : filtrationAt g (i + j) q = filtrationAt g i q := by
  refine le_antisymm ?_ (filtrationAt_mono g (Nat.le_add_right i j) q)
  refine Submodule.span_le.2 ?_
  rintro _ ⟨w, hw, rfl⟩
  exact (inSmoothSpan_of_mem_filtrationFields_add hg hstep j hw).mem_spanAt q

/-- **MLS Exercise 11, p. 351, in module form:** if every field spanning `Δᵢ₊₁` is a smooth
combination of the fields spanning `Δᵢ` (smooth generators), then `Δᵢ` is involutive: the bracket of
two fields spanning `Δᵢ` is a smooth combination of the fields spanning `Δᵢ`. -/
theorem lieBracket_inSmoothSpan_of_step {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    {i : ℕ} (hstep : ∀ w ∈ filtrationFields g (i + 1), InSmoothSpan (filtrationFields g i) w)
    {f h : E → E} (hf : f ∈ filtrationFields g i) (hh : h ∈ filtrationFields g i) :
    InSmoothSpan (filtrationFields g i) (lieBracket ℝ f h) := by
  exact InSmoothSpan.trans (fun w hw => inSmoothSpan_of_mem_filtrationFields_add hg hstep i hw)
    (lieBracket_inSmoothSpan_filtrationFields hg hf hh)

/-- **MLS Exercise 11, p. 351, generator criterion:** under the module form of `Δᵢ₊₁ = Δᵢ`
(smooth generators), the fields spanning `Δᵢ` satisfy the generator criterion of p. 325
everywhere. -/
theorem generatorsInvolutiveOn_of_step {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    {i : ℕ} (hstep : ∀ w ∈ filtrationFields g (i + 1), InSmoothSpan (filtrationFields g i) w) :
    GeneratorsInvolutiveOn (filtrationFields g i) Set.univ := by
  intro q _ f hf h hh
  exact (lieBracket_inSmoothSpan_of_step hg hstep hf hh).mem_spanAt q

/-- **MLS Exercise 11, p. 351, the rank condition:** the module form of `Δᵢ₊₁ = Δᵢ` gives
`rank Δᵢ₊₁(q) = rank Δᵢ(q)` at every point (smooth generators). -/
theorem growth_succ_eq_of_step {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j)) {i : ℕ}
    (hstep : ∀ w ∈ filtrationFields g (i + 1), InSmoothSpan (filtrationFields g i) w) (q : E) :
    growth g (i + 1) q = growth g i q := by
  rw [growth, growth, filtrationAt_add_eq hg hstep 1 q]

end Nonholonomic
end RoboLean
