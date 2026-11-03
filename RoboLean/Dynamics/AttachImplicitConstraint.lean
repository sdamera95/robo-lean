import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The finger configuration of an `attach` from the constraint `h(θ, x) = 0` (MLS p. 305)

MLS Chapter 6, §5.2, printed pp. 304–305: the `attach` operation is given "a constraint between the
configuration variables of the fingers and those of the object ... of the form `h(θ, x) = 0`", with
`J = ∂h/∂θ`, `Gᵀ = −∂h/∂x`, "and we assume that `J` is invertible for the purposes of exposition";
"to read the configuration of the composite robot, we query the state of all the robots ... and
then solve the (holonomic) constraint `h(θ, x) = 0`". The library's `Control.AttachConstraint`
takes the finger configuration `θ = σ(x)` on the constraint as data.

**Formalized: `σ` derived from `h` by the implicit function theorem**, locally, under the rank
hypothesis stated as the hypothesis structure `AttachRegularAt` (`h` strictly differentiable at a
point `(x₀, θ₀)` of the constraint with `∂h/∂θ` invertible, the book's "`J` is invertible"):

* `AttachRegularAt.fingerConfiguration`, Mathlib's implicit function of `h` at `(x₀, θ₀)`, with
  `σ(x₀) = θ₀`, `h(x, σ(x)) = 0` for `x` near `x₀`, and near `(x₀, θ₀)` the constraint holds exactly
  on the graph of `σ` (so "solving the constraint" has exactly one local answer);
* its derivative at `x₀` is `J⁻¹ Gᵀ = −(∂h/∂θ)⁻¹ (∂h/∂x)`, the matrix `J_h⁻¹ Gᵀ` of (6.21)
  (`hasStrictFDerivAt_fingerConfiguration`), and `J (σ′ v) = Gᵀ v` (`fingerPartial_fingerVelocity`);
* along a payload motion through `x₀`, the finger motion `σ ∘ x` obeys the constraint (6.18),
  (6.28) `J θ̇ = Gᵀ ẋ` (`hasDerivAt_fingerConfiguration_comp`).

**Limits.** The implicit function is local: the library's `AttachConstraint` asks for `σ` on all
payload configurations, which the theorem does not give, and the matrices `J(x)`, `G(x)` of
`AttachConstraint` are not identified here with the partial derivatives away from `x₀`. Derivatives
are continuous linear maps on `(Fin p → ℝ) × (Fin n → ℝ)`, payload first; the book's order `h(θ, x)`
is read with `x` first. Nothing here concerns a physical hand.
-/

noncomputable section

open Filter Topology

namespace RoboLean
namespace Control

variable {n p : ℕ}

/-- **The rank hypothesis of the `attach` constraint at a configuration (MLS printed p. 305, "we
assume that `J` is invertible"):** `h(x, θ)` (payload first) is strictly differentiable at
`(x₀, θ₀)` with derivative `deriv`, the point is on the constraint, `h(x₀, θ₀) = 0`, and the partial
derivative `J = ∂h/∂θ` is invertible. -/
structure AttachRegularAt (h : (Fin p → ℝ) × (Fin n → ℝ) → Fin n → ℝ) (x₀ : Fin p → ℝ)
    (θ₀ : Fin n → ℝ) where
  /-- The derivative of `h` at `(x₀, θ₀)` (MLS p. 305). -/
  deriv : (Fin p → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)
  /-- `h` is strictly differentiable at `(x₀, θ₀)` (MLS p. 305). -/
  hasStrictFDerivAt : HasStrictFDerivAt h deriv (x₀, θ₀)
  /-- The point is on the constraint, `h(x₀, θ₀) = 0` (MLS p. 304). -/
  on_constraint : h (x₀, θ₀) = 0
  /-- `J = ∂h/∂θ` is invertible (MLS p. 305). -/
  isInvertible : (deriv ∘L ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin n → ℝ)).IsInvertible

namespace AttachRegularAt

variable {h : (Fin p → ℝ) × (Fin n → ℝ) → Fin n → ℝ} {x₀ : Fin p → ℝ} {θ₀ : Fin n → ℝ}
  (A : AttachRegularAt h x₀ θ₀)

/-- **`J = ∂h/∂θ` (MLS printed p. 305).** -/
def fingerPartial : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  A.deriv ∘L ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin n → ℝ)

/-- **`Gᵀ = −∂h/∂x` (MLS printed p. 305).** -/
def graspTranspose : (Fin p → ℝ) →L[ℝ] (Fin n → ℝ) :=
  -(A.deriv ∘L ContinuousLinearMap.inl ℝ (Fin p → ℝ) (Fin n → ℝ))

/-- **The finger configuration on the constraint (MLS printed p. 305, "solve the (holonomic)
constraint `h(θ, x) = 0`"):** Mathlib's implicit function of `h` at `(x₀, θ₀)`. -/
def fingerConfiguration : (Fin p → ℝ) → Fin n → ℝ :=
  A.hasStrictFDerivAt.implicitFunctionOfProdDomain A.isInvertible

/-- **The finger velocity map `J⁻¹ Gᵀ` (MLS printed p. 278 with p. 305).** -/
def fingerVelocity : (Fin p → ℝ) →L[ℝ] (Fin n → ℝ) :=
  A.fingerPartial.inverse ∘L A.graspTranspose

/-- **Near `(x₀, θ₀)` the constraint holds exactly on the graph of `σ` (MLS printed p. 305).** -/
theorem eventually_constraint_iff :
    ∀ᶠ v in 𝓝 (x₀, θ₀), h v = 0 ↔ A.fingerConfiguration v.1 = v.2 := by
  have := A.hasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain A.isInvertible
  rwa [A.on_constraint] at this

/-- **`σ(x₀) = θ₀` (MLS printed p. 305).** -/
theorem fingerConfiguration_base : A.fingerConfiguration x₀ = θ₀ :=
  (A.eventually_constraint_iff.self_of_nhds).mp A.on_constraint

/-- **The constraint holds on `θ = σ(x)` for `x` near `x₀` (MLS printed p. 304, `h(θ, x) = 0`).** -/
theorem eventually_constraint : ∀ᶠ x in 𝓝 x₀, h (x, A.fingerConfiguration x) = 0 := by
  have := A.hasStrictFDerivAt.eventually_apply_implicitFunctionOfProdDomain A.isInvertible
  rwa [A.on_constraint] at this

/-- **The derivative of `σ` at `x₀` is `J⁻¹ Gᵀ` (MLS printed p. 305 with eq. (6.21), p. 278).** -/
theorem hasStrictFDerivAt_fingerConfiguration :
    HasStrictFDerivAt A.fingerConfiguration A.fingerVelocity x₀ := by
  have := A.hasStrictFDerivAt.hasStrictFDerivAt_implicitFunctionOfProdDomain A.isInvertible
  have e : A.fingerVelocity =
      -(A.deriv ∘L ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin n → ℝ)).inverse ∘L
        (A.deriv ∘L ContinuousLinearMap.inl ℝ (Fin p → ℝ) (Fin n → ℝ)) := by
    rw [fingerVelocity, fingerPartial, graspTranspose, ContinuousLinearMap.comp_neg]
  rw [e]
  exact this

/-- **`J (J⁻¹ Gᵀ v) = Gᵀ v` (MLS printed p. 305, eq. (6.28), p. 284).** -/
theorem fingerPartial_fingerVelocity (v : Fin p → ℝ) :
    A.fingerPartial (A.fingerVelocity v) = A.graspTranspose v := by
  rw [fingerVelocity, ContinuousLinearMap.comp_apply]
  exact A.isInvertible.self_apply_inverse _

/-- **The finger motion of an `attach` obeys the grasp constraint (MLS eq. (6.18), p. 277, and
(6.28), p. 284, with p. 305):** along a payload motion `x` through `x(t) = x₀` with velocity `x'`
at `t`, the finger motion `σ ∘ x` has the velocity `θ' = J⁻¹ Gᵀ x'` at `t`, so `J θ' = Gᵀ x'`. -/
theorem hasDerivAt_fingerConfiguration_comp {x : ℝ → Fin p → ℝ} {x' : Fin p → ℝ} {t : ℝ}
    (hx : HasDerivAt x x' t) (h0 : x t = x₀) :
    HasDerivAt (fun s => A.fingerConfiguration (x s)) (A.fingerVelocity x') t ∧
      A.fingerPartial (A.fingerVelocity x') = A.graspTranspose x' := by
  refine ⟨?_, A.fingerPartial_fingerVelocity x'⟩
  subst h0
  exact A.hasStrictFDerivAt_fingerConfiguration.hasFDerivAt.comp_hasDerivAt t hx

end AttachRegularAt
end Control
end RoboLean
