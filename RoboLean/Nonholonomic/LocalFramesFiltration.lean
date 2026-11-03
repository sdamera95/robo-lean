import RoboLean.Nonholonomic.FiltrationBrackets
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Exercise 11 from equal ranks (MLS p. 351, with p. 340)

**What MLS prints.** Exercise 11 (p. 351): "Let `Δᵢ`, `i = 1, …, κ` be a regular filtration
associated with a distribution. Show that if `rank(Δᵢ₊₁) = rank(Δᵢ)` then `Δᵢ` is involutive.
(Hint: use Exercise 10)", and p. 340: if `rank Δᵢ₊₁ = rank Δᵢ` then `Δᵢ₊ⱼ = Δᵢ` for all `j ≥ 0`.

**Proved here.**

* Local frames for a distribution spanned by any set of fields (`exists_localFrame_of_set`) and,
  for a field taking values in the span of an independent frame near a point, coefficients
  differentiable at the point (`exists_coeffs_of_localFrame`, by inverting `P F(z)` for a left
  inverse `P` of the frame's value `F(y)`).
* For smooth generators and a filtration regular on an open set `U` with
  `rank Δᵢ₊₁ = rank Δᵢ`: `Δᵢ₊ⱼ(y) = Δᵢ(y)` for all `j` and `y ∈ U`
  (`filtrationAt_add_eq_of_growth`), and `Δᵢ` is involutive on `U`
  (`isInvolutiveOn_filtrationAt_of_growth`): a section is near each point a combination of a frame
  of `Δᵢ` with differentiable coefficients, and the frame's brackets lie in `Δ₂ᵢ = Δᵢ` by
  Exercise 10.

**Conventions.** The library's filtration (`filtrationFields`, `filtrationAt`, `growth`), regular
filtrations `IsRegularFiltrationOn g U q₀` (ranks on `U` equal to those at `q₀`), involutivity
`IsInvolutiveOn` with sections differentiable on the set; finite-dimensional `E`.
-/

noncomputable section

open Set Filter Topology VectorField
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A local frame of a regular distribution spanned by a set of fields (MLS p. 325 and
p. 340):** on a finite-dimensional real space, if every field of `S` is continuous at `q` and
`spanAt S` is regular on an open set `U ∋ q`, then some `k = dim Δ_q` fields `v₁, …, v_k` of `S`
are linearly independent and span `spanAt S y` at every point `y` of a neighbourhood `V ⊆ U` of
`q`. -/
theorem exists_localFrame_of_set {S : Set (E → E)} {U : Set E} (hU : IsOpen U)
    (hreg : IsRegularOn (spanAt S) U) {q : E} (hq : q ∈ U) (hS : ∀ f ∈ S, ContinuousAt f q) :
    ∃ (k : ℕ) (v : Fin k → E → E), (∀ i, v i ∈ S) ∧ Module.finrank ℝ (spanAt S q) = k ∧
      ∃ V ∈ 𝓝 q, V ⊆ U ∧ ∀ y ∈ V, LinearIndependent ℝ (fun i => v i y) ∧
        spanAt S y = Submodule.span ℝ (Set.range fun i => v i y) := by
  classical
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' ℝ (fun f : S => (f : E → E) q)
  have : Finite κ := hli.finite
  let : Fintype κ := Fintype.ofFinite κ
  set e := Fintype.equivFin κ
  set v : Fin (Fintype.card κ) → E → E := fun i => (a (e.symm i) : E → E) with hv
  have hvS : ∀ i, v i ∈ S := fun i => (a (e.symm i)).2
  have hliq : LinearIndependent ℝ (fun i => v i q) := hli.comp e.symm e.symm.injective
  have hspq : Submodule.span ℝ (Set.range fun i => v i q) = spanAt S q := by
    have h1 : (Set.range fun i => v i q) = Set.range ((fun f : S => (f : E → E) q) ∘ a) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, rfl⟩
      · rintro ⟨c, rfl⟩
        exact ⟨e c, by simp [hv]⟩
    have h2 : spanAt S q = Submodule.span ℝ (Set.range fun f : S => (f : E → E) q) := by
      rw [spanAt]
      congr 1
      ext x
      simp
    rw [h1, hsp, h2]
  have hk : Module.finrank ℝ (spanAt S q) = Fintype.card κ := by
    rw [← hspq, finrank_span_eq_card hliq, Fintype.card_fin]
  have hcont : ContinuousAt (fun y => fun i => v i y) q :=
    continuousAt_pi.2 fun i => hS _ (hvS i)
  have hev : ∀ᶠ y in 𝓝 q, LinearIndependent ℝ (fun i => v i y) :=
    hcont.eventually hliq.eventually
  obtain ⟨r, hr⟩ := hreg
  refine ⟨Fintype.card κ, v, hvS, hk, {y | LinearIndependent ℝ (fun i => v i y)} ∩ U,
    Filter.inter_mem hev (hU.mem_nhds hq), inter_subset_right, fun y hy => ⟨hy.1, ?_⟩⟩
  have hle : Submodule.span ℝ (Set.range fun i => v i y) ≤ spanAt S y :=
    Submodule.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      exact mem_spanAt (hvS i) y)
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_span_eq_card hy.1, Fintype.card_fin, hr y hy.2, ← hr q hq, hk]

/-- The frame map `a ↦ Σᵢ aᵢ vᵢ(y)` (for MLS p. 325). -/
private def frameMapF {k : ℕ} (v : Fin k → E → E) (y : E) : (Fin k → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).smulRight (v i y)

omit [FiniteDimensional ℝ E] in
private theorem frameMapF_apply {k : ℕ} (v : Fin k → E → E) (y : E) (a : Fin k → ℝ) :
    frameMapF v y a = ∑ i, a i • v i y := by
  simp [frameMapF]

/-- **Coefficients in a local frame (MLS p. 325: a section of `Δ` is a combination of the spanning
fields, here with coefficients differentiable at the point):** on a finite-dimensional real
space, let `v₁, …, v_k` be differentiable at `y` and linearly independent at `y`, and let `w` be
differentiable at `y` with `w(z) ∈ span{v₁(z), …, v_k(z)}` for `z` near `y`. Then there are
functions `c₁, …, c_k`, differentiable at `y`, with `w = Σᵢ cᵢ vᵢ` near `y`. -/
theorem exists_coeffs_of_localFrame {k : ℕ} {v : Fin k → E → E} {w : E → E} {y : E}
    (hv : ∀ i, DifferentiableAt ℝ (v i) y) (hli : LinearIndependent ℝ fun i => v i y)
    (hw : DifferentiableAt ℝ w y)
    (hmem : ∀ᶠ z in 𝓝 y, w z ∈ Submodule.span ℝ (Set.range fun i => v i z)) :
    ∃ c : Fin k → E → ℝ, (∀ i, DifferentiableAt ℝ (c i) y) ∧
      w =ᶠ[𝓝 y] fun z => ∑ i, c i z • v i z := by
  classical
  set G : E → (Fin k → ℝ) →L[ℝ] E := fun z => frameMapF v z with hGdef
  have hG : DifferentiableAt ℝ G y := by
    have : G = fun z => ∑ i, (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) E
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i)) (v i z) := by
      funext z; simp [hGdef, frameMapF]
    rw [this]
    exact DifferentiableAt.fun_sum fun i _ => ((ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) E
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i)).differentiableAt).comp y
        (hv i)
  have hGy : LinearMap.ker (G y : (Fin k → ℝ) →ₗ[ℝ] E) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro a ha
    have h0 : ∑ i, a i • v i y = 0 := by rw [← frameMapF_apply]; exact ha
    exact funext fun i => Fintype.linearIndependent_iff.1 hli a h0 i
  obtain ⟨P', hP'⟩ := LinearMap.exists_leftInverse_of_injective _ hGy
  set P : E →L[ℝ] (Fin k → ℝ) := LinearMap.toContinuousLinearMap P' with hPdef
  have hPG : ∀ a, P (G y a) = a := fun a => by
    have := congrArg (fun L : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ) => L a) hP'
    simpa [hPdef] using this
  set M : E → (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) := fun z => P.comp (G z) with hMdef
  have hM : DifferentiableAt ℝ M y :=
    ((ContinuousLinearMap.compL ℝ (Fin k → ℝ) E (Fin k → ℝ)) P).differentiableAt.comp y hG
  have hMy : M y = 1 := by ext1 a; simp [hMdef, hPG]
  have hunit : ∀ᶠ z in 𝓝 y, IsUnit (M z) := by
    exact hM.continuousAt.eventually_mem
      ((Units.isOpen (R := (Fin k → ℝ) →L[ℝ] (Fin k → ℝ))).mem_nhds (by rw [hMy]; exact isUnit_one))
  have hinv : DifferentiableAt ℝ (fun z => Ring.inverse (M z)) y := by
    have h := (contDiffAt_ringInverse ℝ (n := 1) (1 : ((Fin k → ℝ) →L[ℝ] (Fin k → ℝ))ˣ)).differentiableAt
      one_ne_zero
    rw [Units.val_one, ← hMy] at h
    exact h.comp y hM
  set c : Fin k → E → ℝ := fun i z => Ring.inverse (M z) (P (w z)) i with hcdef
  have hc : ∀ i, DifferentiableAt ℝ (c i) y := fun i => by
    have h := hinv.clm_apply (P.differentiableAt.comp y hw)
    exact (differentiableAt_pi.1 h) i
  refine ⟨c, hc, ?_⟩
  filter_upwards [hunit, hmem] with z hu hz
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hz
  have hGa : G z a = w z := by rw [hGdef, frameMapF_apply]; exact ha
  have hca : (fun i => c i z) = a := by
    have h1 : P (w z) = M z a := by rw [← hGa]; rfl
    have h2 := congrArg (fun L : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) => L a)
      (Ring.inverse_mul_cancel (M z) hu)
    simp only [mul_apply_eq_comp, one_apply_eq_self] at h2
    funext i
    simp only [hcdef, h1, h2]
  calc w z = ∑ i, a i • v i z := ha.symm
    _ = ∑ i, c i z • v i z := by rw [← hca]

variable {m : ℕ}

/-- `Δᵢ₊₁ = Δᵢ` on the set from the rank equality (MLS p. 340). -/
private theorem filtrationAt_succ_eq {g : Fin m → E → E} {U : Set E} {q₀ : E}
    (hreg : IsRegularFiltrationOn g U q₀) {i : ℕ} (hrank : growth g (i + 1) q₀ = growth g i q₀)
    {y : E} (hy : y ∈ U) : filtrationAt g (i + 1) y = filtrationAt g i y := by
  refine (Submodule.eq_of_le_of_finrank_eq (filtrationAt_mono g (Nat.le_succ i) y) ?_).symm
  have h1 := hreg i y hy
  have h2 := hreg (i + 1) y hy
  simp only [growth] at h1 h2 hrank
  rw [h1, h2, hrank]

/-- **MLS p. 340, "`Δᵢ₊ⱼ = Δᵢ` for all `j ≥ 0`", from equal ranks of a regular filtration:** on a
finite-dimensional real space, for smooth generators and a filtration regular on an open set `U`
(`IsRegularFiltrationOn g U q₀`) with `rank Δᵢ₊₁(q₀) = rank Δᵢ(q₀)`, `Δᵢ₊ⱼ(y) = Δᵢ(y)` for all
`j` and all `y ∈ U`. -/
theorem filtrationAt_add_eq_of_growth {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    {U : Set E} (hU : IsOpen U) {q₀ : E} (hreg : IsRegularFiltrationOn g U q₀) {i : ℕ}
    (hrank : growth g (i + 1) q₀ = growth g i q₀) (j : ℕ) :
    ∀ y ∈ U, filtrationAt g (i + j) y = filtrationAt g i y := by
  have hsmooth : ∀ {n : ℕ} {f : E → E}, f ∈ filtrationFields g n → ContDiff ℝ ∞ f :=
    fun hf => contDiff_of_mem_filtrationFields hg hf
  have hregi : IsRegularOn (spanAt (filtrationFields g i)) U :=
    ⟨growth g i q₀, fun y hy => hreg i y hy⟩
  induction j with
  | zero => intro y _; rfl
  | succ j ih =>
    intro y hy
    refine le_antisymm ?_ (filtrationAt_mono g (Nat.le_add_right i (j + 1)) y)
    rw [filtrationAt, spanAt, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    rw [show i + (j + 1) = (i + j) + 1 from rfl] at hf
    have hgen : ∀ a, g a y ∈ filtrationAt g i y := fun a => by
      have h1 : g a ∈ filtrationFields g (i + 1) :=
        filtrationFields_mono g (i := 1) (j := i + 1) (by omega)
          (by rw [filtrationFields_one]; exact ⟨a, rfl⟩)
      have h2 := mem_spanAt h1 y
      rw [← filtrationAt, filtrationAt_succ_eq hreg hrank hy] at h2
      exact h2
    rcases hf with ⟨a, rfl⟩ | ⟨a, w, hw, rfl⟩
    · -- a generator lies in `Δᵢ₊₁ = Δᵢ`
      exact hgen a
    · -- `[g_a, w]` with `w` a combination of a frame of `Δᵢ` near `y`
      obtain ⟨k, v, hvS, -, V, hV, hVU, hframe⟩ := exists_localFrame_of_set hU hregi hy
        fun f hf => (hsmooth hf).continuous.continuousAt
      have hvd : ∀ b, DifferentiableAt ℝ (v b) y := fun b =>
        ((hsmooth (hvS b)).differentiable (by simp)) y
      have hmem : ∀ᶠ z in 𝓝 y, w z ∈ Submodule.span ℝ (Set.range fun b => v b z) := by
        filter_upwards [hV] with z hz
        have h1 := mem_spanAt hw z
        rw [← filtrationAt, ih z (hVU hz), filtrationAt, (hframe z hz).2] at h1
        exact h1
      obtain ⟨c, hc, hwc⟩ := exists_coeffs_of_localFrame hvd (hframe y (mem_of_mem_nhds hV)).1
        (((hsmooth hw).differentiable (by simp)) y) hmem
      have hga : g a =ᶠ[𝓝 y] fun x => ∑ _b : Fin 1, (fun _ : E => (1 : ℝ)) x • g a x :=
        Eventually.of_forall fun x => by simp
      have hgd : DifferentiableAt ℝ (g a) y := ((hg a).differentiable (by simp)) y
      simp only [SetLike.mem_coe]
      rw [hga.lieBracket_vectorField_eq hwc,
        lieBracket_sum_smul_sum_smul (u := fun _ : Fin 1 => g a) (fun _ => hgd) hvd
          (fun _ => differentiableAt_const _) hc]
      have hsucc : ∀ b, lieBracket ℝ (g a) (v b) y ∈ filtrationAt g i y := fun b => by
        have h1 := mem_spanAt (lieBracket_mem_filtrationFields g a (hvS b)) y
        rw [← filtrationAt, filtrationAt_succ_eq hreg hrank hy] at h1
        exact h1
      refine Submodule.sub_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
        refine Submodule.sum_mem _ fun _ _ => Submodule.sum_mem _ fun b _ =>
          Submodule.smul_mem _ _ ?_
      · exact hsucc b
      · exact mem_spanAt (hvS b) y
      · exact hgen a

/-- **MLS Exercise 11, p. 351, from equal ranks:** on a finite-dimensional real space, for smooth
generators and a filtration regular on an open set `U` (`IsRegularFiltrationOn g U q₀`, MLS: a
regular filtration) with `rank Δᵢ₊₁(q₀) = rank Δᵢ(q₀)`, the distribution `Δᵢ` is involutive on
`U` (sections differentiable on `U`). -/
theorem isInvolutiveOn_filtrationAt_of_growth {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    {U : Set E} (hU : IsOpen U) {q₀ : E} (hreg : IsRegularFiltrationOn g U q₀) {i : ℕ}
    (hrank : growth g (i + 1) q₀ = growth g i q₀) : IsInvolutiveOn (filtrationAt g i) U := by
  have hsmooth : ∀ {n : ℕ} {f : E → E}, f ∈ filtrationFields g n → ContDiff ℝ ∞ f :=
    fun hf => contDiff_of_mem_filtrationFields hg hf
  have hregi : IsRegularOn (spanAt (filtrationFields g i)) U :=
    ⟨growth g i q₀, fun y hy => hreg i y hy⟩
  intro f h hf hh hfD hhD y hy
  obtain ⟨k, v, hvS, -, V, hV, hVU, hframe⟩ := exists_localFrame_of_set hU hregi hy
    fun f hf => (hsmooth hf).continuous.continuousAt
  have hvd : ∀ b, DifferentiableAt ℝ (v b) y := fun b =>
    ((hsmooth (hvS b)).differentiable (by simp)) y
  have hmemof : ∀ s : E → E, (∀ x ∈ U, s x ∈ filtrationAt g i x) →
      ∀ᶠ z in 𝓝 y, s z ∈ Submodule.span ℝ (Set.range fun b => v b z) := fun s hs => by
    filter_upwards [hV] with z hz
    have h1 := hs z (hVU hz)
    rw [filtrationAt, (hframe z hz).2] at h1
    exact h1
  have hli := (hframe y (mem_of_mem_nhds hV)).1
  obtain ⟨α, hα, hfα⟩ := exists_coeffs_of_localFrame hvd hli (hf y hy) (hmemof f hfD)
  obtain ⟨β, hβ, hhβ⟩ := exists_coeffs_of_localFrame hvd hli (hh y hy) (hmemof h hhD)
  have hgen : GeneratorsInvolutiveOn (Set.range v) {y} := by
    rintro z hz _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [mem_singleton_iff.1 hz]
    have h1 := lieBracket_mem_filtrationAt hg (hvS a) (hvS b) y
    rw [filtrationAt_add_eq_of_growth hg hU hreg hrank i y hy, filtrationAt,
      (hframe y (mem_of_mem_nhds hV)).2, ← spanAt_range] at h1
    exact h1
  have h := hgen.lieBracket_mem (mem_singleton y) hvd hα hβ hfα hhβ
  rw [spanAt_range, ← (hframe y (mem_of_mem_nhds hV)).2] at h
  exact h

end Nonholonomic
end RoboLean
