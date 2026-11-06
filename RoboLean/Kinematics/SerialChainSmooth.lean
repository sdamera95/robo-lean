import RoboLean.Geometry.ExpSmooth
import RoboLean.Kinematics.SerialChain

/-!
# Smoothness of the product-of-exponentials forward kinematics

MLS Chapter 3, §2.2 and §4.1, printed pp. 85–87 and 115. The forward kinematics of an open chain
is the map `g_st : Q → SE(3)`, `g_st(θ) = e^{ξ̂₁θ₁} ⋯ e^{ξ̂ₙθₙ} g_st(0)` (eq. (3.3), p. 87). On
p. 115 the book differentiates it as a matrix-valued function, `V̂ˢ_st = Σᵢ (∂g_st/∂θᵢ) θ̇ᵢ
g_st⁻¹(θ)` "applying the chain rule" (eq. (3.51)), and forms the columns `(∂g_st/∂θᵢ g_st⁻¹)^∨` of
the spatial Jacobian (eq. (3.52)); on p. 255 it uses that "`g_{pfᵢ}` is a smooth function of `θ`".
Smoothness of `g_st` is used, not stated, in the book.

**Formalized.** For every chain `c : SerialChain n` (arbitrary twists, real joint coordinates
`θ : Fin n → ℝ`, MLS p. 84 with the real lift of the library) and every order `k : WithTop ℕ∞`
(`k = ∞` is `C^∞`, `k = ω` analytic):

* every entry of the homogeneous matrix `[R p; 0 1]` of the product of exponentials
  `exp(ξ₁θ₁) ⋯ exp(ξₙθₙ)` is `C^k` in `θ` (`SerialChain.contDiff_poe_toHomogeneous`), and so is
  every entry of the forward kinematics `g_st(θ)` (`SerialChain.contDiff_fk_toHomogeneous`);
* the rotation entries and the translation of `g_st(θ)` are `C^k` in `θ`
  (`SerialChain.contDiff_fk_rotation`, `SerialChain.contDiff_fk_translation`);
* the adjacent-frame forward kinematics of eq. (3.1), p. 85, is `C^k`
  (`LinkFrameChain.contDiff_fk_toHomogeneous`), through its equality with the product of
  exponentials.

No joint type or unit-axis premise is needed. Derivative identities between these maps and the
spatial or body Jacobians are not stated here; the library's Jacobian statements are along
trajectories (`SerialChain.hasDerivAt_fk_toHomogeneous`).
-/

noncomputable section

namespace RoboLean

namespace SerialChain

variable {n : ℕ} {k : WithTop ℕ∞}

/-- **The product of exponentials is smooth in the joint coordinates (MLS eq. (3.3), p. 87,
differentiated in eqs. (3.51)–(3.52), p. 115).** For every chain, every entry of the homogeneous
matrix of `exp(ξ₁θ₁) ⋯ exp(ξₙθₙ)` is a `C^k` function of `θ ∈ ℝⁿ`, for every order `k`. -/
theorem contDiff_poe_toHomogeneous (c : SerialChain n) (i j : HomogeneousIndex) :
    ContDiff ℝ k fun θ : Fin n → ℝ => (c.poe θ).toHomogeneous i j :=
  RigidTransform.contDiff_toHomogeneous_list_prod
    (fun l a b => (Twist.contDiff_exp_toHomogeneous_apply (c.twist l) a b).comp
      (contDiff_apply ℝ _ l)) i j

/-- **The forward kinematics map is smooth (MLS eq. (3.3), p. 87, differentiated in eqs.
(3.51)–(3.52), p. 115; p. 255, "`g_{pfᵢ}` is a smooth function of `θ`").** For every chain, every
entry of the homogeneous matrix of `g_st(θ) = exp(ξ₁θ₁) ⋯ exp(ξₙθₙ) g_st(0)` is a `C^k` function
of `θ ∈ ℝⁿ`, for every order `k`. -/
theorem contDiff_fk_toHomogeneous (c : SerialChain n) (i j : HomogeneousIndex) :
    ContDiff ℝ k fun θ : Fin n → ℝ => (c.fk θ).toHomogeneous i j :=
  RigidTransform.contDiff_toHomogeneous_mul (fun a b => c.contDiff_poe_toHomogeneous a b)
    (fun _ _ => contDiff_const) i j

/-- **The orientation of the tool is smooth in the joint coordinates (MLS eq. (3.3), p. 87, with
`g_st(θ) = [R(θ) p(θ); 0 1]`, p. 88).** Every entry of the rotation `R(θ)` of the forward
kinematics is a `C^k` function of `θ`, for every order `k`. -/
theorem contDiff_fk_rotation (c : SerialChain n) (i j : Fin 3) :
    ContDiff ℝ k fun θ : Fin n → ℝ => (c.fk θ).rotation.val i j :=
  (RigidTransform.contDiff_toHomogeneous_iff.mp fun a b => c.contDiff_fk_toHomogeneous a b).1 i j

/-- **The position of the tool is smooth in the joint coordinates (MLS eq. (3.3), p. 87, with
`g_st(θ) = [R(θ) p(θ); 0 1]`, p. 88).** The translation `p(θ)` of the forward kinematics is a
`C^k` map `ℝⁿ → ℝ³`, for every order `k`. -/
theorem contDiff_fk_translation (c : SerialChain n) :
    ContDiff ℝ k fun θ : Fin n → ℝ => (c.fk θ).translation :=
  (RigidTransform.contDiff_toHomogeneous_iff.mp fun a b => c.contDiff_fk_toHomogeneous a b).2

end SerialChain

namespace LinkFrameChain

variable {n : ℕ} {k : WithTop ℕ∞}

/-- **The adjacent-frame forward kinematics is smooth (MLS eq. (3.1), p. 85, equal to the product
of exponentials by eqs. (3.7)–(3.10), p. 94).** Every entry of the homogeneous matrix of
`g_{s l₁}(θ₁) ⋯ g_{lₙ₋₁ lₙ}(θₙ) g_{lₙ t}` is a `C^k` function of `θ`, for every order `k`. -/
theorem contDiff_fk_toHomogeneous (c : LinkFrameChain n) (i j : HomogeneousIndex) :
    ContDiff ℝ k fun θ : Fin n → ℝ => (c.fk θ).toHomogeneous i j := by
  simp only [fk_eq_toSerialChain_fk]
  exact c.toSerialChain.contDiff_fk_toHomogeneous i j

end LinkFrameChain

end RoboLean
