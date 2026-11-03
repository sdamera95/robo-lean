import RoboLean.Dynamics.Tendons

/-!
# The tendon networks of MLS Chapter 6, Exercise 6 (printed p. 315)

MLS Chapter 6, Exercise 6, printed p. 315: "Derive the actuator kinematics for the tendon networks
shown below. Consider both the rigid and elastic cases." The figure shows two planar two-joint
fingers, (a) with three tendons and (b) with two tendons and a spring between the links; no
dimensions are printed.

**Reading of the figure (a convention of this file).** Joint angles `θ₁, θ₂` are relative angles,
positive counterclockwise in the figure; the pulleys at joints 1 and 2 have radii `r₁, r₂`. As on
MLS p. 294, the extension `hᵢ(θ) = lᵢ ± rᵢ₁ θ₁ ± rᵢ₂ θ₂` is the length of the tendon path, with `+`
when the path lengthens under a positive rotation: a tendon passing a joint on the lower side of its
pulley, or wrapping counterclockwise onto a pulley it is attached to, gains `r θ`; on the upper side,
or wrapping clockwise, it loses `r θ`. Crossings on the base or along link 1 change no length.

* (a) Tendon 1 (middle actuator) runs over the top of the joint-1 pulley and is attached to it,
  wrapping clockwise: `h₁ = l₁ − r₁ θ₁`. Tendon 2 (top actuator) crosses to the lower side of the
  joint-1 pulley, crosses between the joints to the top of the joint-2 pulley and is attached to
  it, wrapping clockwise: `h₂ = l₂ + r₁ θ₁ − r₂ θ₂`. Tendon 3 (bottom actuator) crosses to the upper
  side of the joint-1 pulley and then to the lower side of the joint-2 pulley, wrapping
  counterclockwise: `h₃ = l₃ − r₁ θ₁ + r₂ θ₂`.
* (b) Tendon 1 (lower actuator) as tendon 1 of (a): `h₁ = l₁ − r₁ θ₁`; tendon 2 (upper actuator) as
  tendon 2 of (a): `h₂ = l₂ + r₁ θ₁ − r₂ θ₂`. The spring between link 1 and link 2 is not an actuator
  and is not part of the actuator kinematics; it enters the dynamics as a passive joint torque and
  is not modeled here (its attachment points are not dimensioned).

**Results.** For both networks the coupling matrix `P = (∂h/∂θ)ᵀ` (rigid case, `τ = P f`) and, for
elastic tendons with stiffnesses `kᵢ` (`K = diag(k)`), the coupling `Q = P K` between commanded
extensions and joint torques and the stiffness `S(θ) = P K Pᵀ θ` (p. 297). Under this reading
neither network is force-closure (6.34): in (a) tendons 2 and 3 pull in exactly opposite directions,
and (b) has fewer than `n + 1 = 3` tendons; in (b), `P` is invertible when `r₁ r₂ ≠ 0`, so tensions
are determined by torques. These conclusions depend on the reading, not on a printed statement.

Kinematics and statics only; nothing here models friction, slack tendons or a physical hand.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace Composite

/-! ### Network (a): three tendons -/

/-- **The extension functions of MLS Chapter 6, Exercise 6(a), p. 315**, in the reading of this
file: `h = (l₁ − r₁ θ₁, l₂ + r₁ θ₁ − r₂ θ₂, l₃ − r₁ θ₁ + r₂ θ₂)` (path lengths, `θ` counterclockwise,
pulley radii `r₁, r₂`). -/
def tendonNetworkA (l : Fin 3 → ℝ) (r₁ r₂ : ℝ) (θ : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![l 0 - r₁ * θ 0, l 1 + r₁ * θ 0 - r₂ * θ 1, l 2 - r₁ * θ 0 + r₂ * θ 1]

/-- The coupling matrix of MLS Chapter 6, Exercise 6(a) (p. 315) in this file's reading:
`P = [[−r₁, r₁, −r₁], [0, −r₂, r₂]]`, columns indexed by the tendons. -/
def tendonCouplingA (r₁ r₂ : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![-r₁, r₁, -r₁; 0, -r₂, r₂]

private theorem tendonNetworkA_eq (l : Fin 3 → ℝ) (r₁ r₂ : ℝ) :
    tendonNetworkA l r₁ r₂ = fun q => l + (tendonCouplingA r₁ r₂)ᵀ *ᵥ q := by
  funext q i
  fin_cases i <;>
    simp [tendonNetworkA, tendonCouplingA, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- **MLS Chapter 6, Exercise 6(a), p. 315, rigid tendons:** the coupling matrix
`P(θ) = (∂h/∂θ)ᵀ` (MLS p. 295) of the network is the constant `[[−r₁, r₁, −r₁], [0, −r₂, r₂]]` at
every configuration, so `τ = P f` gives `τ₁ = r₁ (−f₁ + f₂ − f₃)`, `τ₂ = r₂ (f₃ − f₂)`. -/
theorem couplingMatrix_tendonNetworkA (l : Fin 3 → ℝ) (r₁ r₂ : ℝ) (θ : Fin 2 → ℝ) :
    couplingMatrix (tendonNetworkA l r₁ r₂) θ = tendonCouplingA r₁ r₂ := by
  rw [tendonNetworkA_eq, couplingMatrix_affine, Matrix.transpose_transpose]

/-- **MLS Chapter 6, Exercise 6(a), p. 315: the joint torques of the tendon tensions**,
`τ = P f = (r₁ (−f₁ + f₂ − f₃), r₂ (f₃ − f₂))`. -/
theorem tendonCouplingA_mulVec (r₁ r₂ : ℝ) (f : Fin 3 → ℝ) :
    tendonCouplingA r₁ r₂ *ᵥ f = ![r₁ * (-f 0 + f 1 - f 2), r₂ * (f 2 - f 1)] := by
  funext i
  fin_cases i <;> simp [tendonCouplingA, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- **MLS Chapter 6, Exercise 6(a), p. 315, elastic tendons (MLS p. 297):** with tendon stiffnesses
`K = diag(k₁, k₂, k₃)`, the coupling between commanded extensions and joint torques is
`Q = P K = [[−r₁ k₁, r₁ k₂, −r₁ k₃], [0, −r₂ k₂, r₂ k₃]]`. -/
theorem tendonCouplingA_mul_diagonal (r₁ r₂ : ℝ) (k : Fin 3 → ℝ) :
    tendonCouplingA r₁ r₂ * Matrix.diagonal k =
      !![-r₁ * k 0, r₁ * k 1, -r₁ * k 2; 0, -r₂ * k 1, r₂ * k 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tendonCouplingA, Matrix.mul_apply, Fin.sum_univ_three]

/-- **MLS Chapter 6, Exercise 6(a), p. 315, elastic tendons: the stiffness**
`S(θ) = P K (h(θ) − h(0))` (MLS p. 297) with `K = diag(k₁, k₂, k₃)` is
`(r₁² (k₁ + k₂ + k₃) θ₁ − r₁ r₂ (k₂ + k₃) θ₂, −r₁ r₂ (k₂ + k₃) θ₁ + r₂² (k₂ + k₃) θ₂)`. -/
theorem tendonStiffness_tendonNetworkA (l : Fin 3 → ℝ) (r₁ r₂ : ℝ) (k : Fin 3 → ℝ)
    (θ : Fin 2 → ℝ) :
    tendonStiffness (couplingMatrix (tendonNetworkA l r₁ r₂) θ) (Matrix.diagonal k)
        (tendonNetworkA l r₁ r₂) θ =
      ![r₁ ^ 2 * (k 0 + k 1 + k 2) * θ 0 - r₁ * r₂ * (k 1 + k 2) * θ 1,
        -(r₁ * r₂ * (k 1 + k 2) * θ 0) + r₂ ^ 2 * (k 1 + k 2) * θ 1] := by
  rw [couplingMatrix_tendonNetworkA]
  funext i
  fin_cases i <;>
    simp [tendonStiffness, tendonNetworkA, tendonCouplingA, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- **MLS Chapter 6, Exercise 6(a), p. 315, elastic dynamics:** with elastic tendons
`f = K (e + h(0) − h(θ))`, the dynamics `M θ̈ + C θ̇ + N = P f` of the finger are
`M θ̈ + C θ̇ + N + S(θ) = Q e` (MLS p. 297) with `P`, `Q` and `S` as computed for this network. -/
theorem elastic_dynamics_tendonNetworkA (M C : Matrix (Fin 2) (Fin 2) ℝ) (N θ' θ'' : Fin 2 → ℝ)
    (l : Fin 3 → ℝ) (r₁ r₂ : ℝ) (k e : Fin 3 → ℝ) (θ : Fin 2 → ℝ) :
    M *ᵥ θ'' + C *ᵥ θ' + N =
        tendonCouplingA r₁ r₂ *ᵥ elasticForce (Matrix.diagonal k) (tendonNetworkA l r₁ r₂) e θ ↔
      M *ᵥ θ'' + C *ᵥ θ' + N +
          ![r₁ ^ 2 * (k 0 + k 1 + k 2) * θ 0 - r₁ * r₂ * (k 1 + k 2) * θ 1,
            -(r₁ * r₂ * (k 1 + k 2) * θ 0) + r₂ ^ 2 * (k 1 + k 2) * θ 1] =
        !![-r₁ * k 0, r₁ * k 1, -r₁ * k 2; 0, -r₂ * k 1, r₂ * k 2] *ᵥ e := by
  have h := elastic_dynamics_iff M C N θ' θ'' (couplingMatrix (tendonNetworkA l r₁ r₂) θ)
    (Matrix.diagonal k) (tendonNetworkA l r₁ r₂) e θ
  rw [tendonStiffness_tendonNetworkA, couplingMatrix_tendonNetworkA,
    tendonCouplingA_mul_diagonal] at h
  exact h

/-- **Network (a) of MLS Chapter 6, Exercise 6 is not force-closure (eq. (6.34), p. 299) in this
file's reading**, for positive pulley radii: tendons 2 and 3 have opposite columns
`(r₁, −r₂)` and `(−r₁, r₂)`, so no positive tensions give the torque `(1, 0)`. A consequence of the
reading of the figure, not a printed claim. -/
theorem not_isTendonForceClosure_tendonCouplingA {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    ¬ IsTendonForceClosure (tendonCouplingA r₁ r₂) := by
  intro h
  obtain ⟨f, hf, hpos⟩ := h ![1, 0]
  rw [tendonCouplingA_mulVec] at hf
  have h0 := congrFun hf 0
  have h1 := congrFun hf 1
  simp at h0 h1
  have h21 : f 2 = f 1 := by
    rcases h1 with h1 | h1
    · exact absurd h1 hr₂.ne'
    · linarith
  rw [h21] at h0
  nlinarith [hpos 0]

/-! ### Network (b): two tendons -/

/-- **The extension functions of MLS Chapter 6, Exercise 6(b), p. 315**, in the reading of this
file: `h = (l₁ − r₁ θ₁, l₂ + r₁ θ₁ − r₂ θ₂)`; the spring between the links is not an actuator and
is not included. -/
def tendonNetworkB (l : Fin 2 → ℝ) (r₁ r₂ : ℝ) (θ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![l 0 - r₁ * θ 0, l 1 + r₁ * θ 0 - r₂ * θ 1]

/-- The coupling matrix of MLS Chapter 6, Exercise 6(b) (p. 315) in this file's reading:
`P = [[−r₁, r₁], [0, −r₂]]`. -/
def tendonCouplingB (r₁ r₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-r₁, r₁; 0, -r₂]

private theorem tendonNetworkB_eq (l : Fin 2 → ℝ) (r₁ r₂ : ℝ) :
    tendonNetworkB l r₁ r₂ = fun q => l + (tendonCouplingB r₁ r₂)ᵀ *ᵥ q := by
  funext q i
  fin_cases i <;>
    simp [tendonNetworkB, tendonCouplingB, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- **MLS Chapter 6, Exercise 6(b), p. 315, rigid tendons:** the coupling matrix of the network is
the constant `[[−r₁, r₁], [0, −r₂]]`, so `τ = P f = (r₁ (f₂ − f₁), −r₂ f₂)`. -/
theorem couplingMatrix_tendonNetworkB (l : Fin 2 → ℝ) (r₁ r₂ : ℝ) (θ : Fin 2 → ℝ) :
    couplingMatrix (tendonNetworkB l r₁ r₂) θ = tendonCouplingB r₁ r₂ := by
  rw [tendonNetworkB_eq, couplingMatrix_affine, Matrix.transpose_transpose]

/-- **MLS Chapter 6, Exercise 6(b), p. 315: the joint torques of the tendon tensions**,
`τ = P f = (r₁ (f₂ − f₁), −r₂ f₂)`. -/
theorem tendonCouplingB_mulVec (r₁ r₂ : ℝ) (f : Fin 2 → ℝ) :
    tendonCouplingB r₁ r₂ *ᵥ f = ![r₁ * (f 1 - f 0), -(r₂ * f 1)] := by
  funext i
  fin_cases i
  · simp [tendonCouplingB, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [tendonCouplingB, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **MLS Chapter 6, Exercise 6(b), p. 315:** `det P = r₁ r₂`, so for nonzero radii the tendon
tensions are determined by the joint torques, `f = P⁻¹ τ`. -/
theorem det_tendonCouplingB (r₁ r₂ : ℝ) : (tendonCouplingB r₁ r₂).det = r₁ * r₂ := by
  simp [tendonCouplingB, Matrix.det_fin_two]

/-- **MLS Chapter 6, Exercise 6(b), p. 315, elastic tendons (MLS p. 297):** with tendon stiffnesses
`K = diag(k₁, k₂)`, `Q = P K = [[−r₁ k₁, r₁ k₂], [0, −r₂ k₂]]` and the stiffness
`S(θ) = P K (h(θ) − h(0)) = (r₁² (k₁ + k₂) θ₁ − r₁ r₂ k₂ θ₂, −r₁ r₂ k₂ θ₁ + r₂² k₂ θ₂)`. -/
theorem tendonStiffness_tendonNetworkB (l : Fin 2 → ℝ) (r₁ r₂ : ℝ) (k : Fin 2 → ℝ)
    (θ : Fin 2 → ℝ) :
    tendonCouplingB r₁ r₂ * Matrix.diagonal k = !![-r₁ * k 0, r₁ * k 1; 0, -r₂ * k 1] ∧
      tendonStiffness (couplingMatrix (tendonNetworkB l r₁ r₂) θ) (Matrix.diagonal k)
          (tendonNetworkB l r₁ r₂) θ =
        ![r₁ ^ 2 * (k 0 + k 1) * θ 0 - r₁ * r₂ * k 1 * θ 1,
          -(r₁ * r₂ * k 1 * θ 0) + r₂ ^ 2 * k 1 * θ 1] := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [tendonCouplingB, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [couplingMatrix_tendonNetworkB]
    funext i
    fin_cases i <;>
      simp [tendonStiffness, tendonNetworkB, tendonCouplingB, Matrix.mulVec, dotProduct,
        Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Network (b) of MLS Chapter 6, Exercise 6 is not force-closure (eq. (6.34), p. 299)**: it has
two tendons for two joints, fewer than the `n + 1 = 3` that force-closure needs (p. 299,
`IsTendonForceClosure.succ_le_card`); the spring of the figure supplies the antagonistic torque. -/
theorem not_isTendonForceClosure_tendonCouplingB (r₁ r₂ : ℝ) :
    ¬ IsTendonForceClosure (tendonCouplingB r₁ r₂) := by
  intro h
  have := h.succ_le_card (by norm_num)
  simp at this

end Composite
end RoboLean
