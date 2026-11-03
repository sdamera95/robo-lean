import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# One-forms and their pull back

MLS Appendix A, §1.5, printed p. 408. A smooth one-form on `M` is a smooth section `α : M → T*M`,
in local coordinates `α(x) = α₁(x)dx₁ + ⋯ + αₙ(x)dxₙ`. For a smooth map `F : M → N` and a one-form
`β` on `N`, the pull back `α = F*β` is defined by `⟨α_p, X_p⟩ = ⟨β_{F(p)}, F_{*p}X_p⟩`; "the pull
back of a one-form is defined for any smooth mapping `F : M → N`, not just diffeomorphisms".

Reading. As for the vector fields of the library (Chapter 7), manifolds are real normed spaces `E`,
tangent vectors at `p` are elements of `E`, covectors are continuous linear functionals
`E →L[ℝ] ℝ`, a one-form is a map `E → (E →L[ℝ] ℝ)`, and `F_{*p}` is the Fréchet derivative of `F`
at `p`. The pull back is defined for every map `F` (no invertibility); the statements give its
defining pairing, its compatibility with composition, `(G ∘ F)* = F* G*`, and that it sends the
differential `df` of a function to the differential of `f ∘ F`, for differentiable maps.
Smoothness of the forms is not part of the definition here.
-/

noncomputable section

namespace RoboLean

namespace LieGroup

variable {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']

/-- **The pull back of a one-form** (MLS §1.5, p. 408): for `F : E → E'` and a one-form
`β : E' → (E' →L[ℝ] ℝ)`, `(F*β)_p = β_{F(p)} ∘ F_{*p}`, defined for every map `F`. -/
def pullbackOneForm (F : E → E') (β : E' → E' →L[ℝ] ℝ) (p : E) : E →L[ℝ] ℝ :=
  (β (F p)).comp (fderiv ℝ F p)

/-- MLS p. 408: the defining pairing `⟨(F*β)_p, X_p⟩ = ⟨β_{F(p)}, F_{*p}X_p⟩`. -/
theorem pullbackOneForm_apply (F : E → E') (β : E' → E' →L[ℝ] ℝ) (p X : E) :
    pullbackOneForm F β p X = β (F p) (fderiv ℝ F p X) := rfl

/-- MLS p. 408: pull backs compose contravariantly, `(G ∘ F)*γ = F*(G*γ)`, for maps differentiable
at the points involved (the chain rule `(G ∘ F)_{*p} = G_{*F(p)} F_{*p}`, p. 405). -/
theorem pullbackOneForm_comp (F : E → E') (G : E' → E'') (γ : E'' → E'' →L[ℝ] ℝ) (p : E)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G (F p)) :
    pullbackOneForm (G ∘ F) γ p = pullbackOneForm F (pullbackOneForm G γ) p := by
  unfold pullbackOneForm
  rw [fderiv_comp p hG hF, Function.comp_apply, ContinuousLinearMap.comp_assoc]

/-- MLS p. 408: the pull back of the differential `df` (the one-form `q ↦ Df(q)`) is the
differential of `f ∘ F`, for `F` differentiable at `p` and `f` differentiable at `F(p)`. -/
theorem pullbackOneForm_fderiv (F : E → E') (f : E' → ℝ) (p : E)
    (hF : DifferentiableAt ℝ F p) (hf : DifferentiableAt ℝ f (F p)) :
    pullbackOneForm F (fun q => fderiv ℝ f q) p = fderiv ℝ (f ∘ F) p := by
  unfold pullbackOneForm
  rw [fderiv_comp p hf hF]

end LieGroup

end RoboLean
