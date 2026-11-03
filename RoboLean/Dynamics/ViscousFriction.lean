import RoboLean.Control.RobotAugmentedPD
import RoboLean.Dynamics.Lagrangian

/-!
# Viscous joint friction and end-effector forces in `N` (MLS p. 170)

MLS Chapter 4, §3.1, printed p. 170: "Let `τᵢ` represent the applied torque at the joint and define
`−Nᵢ(θ, θ̇)` to be any other forces which act on the `i`th generalized coordinate, including
conservative forces arising from a potential as well as frictional forces. ... if the manipulator
has viscous friction at the joints, then `Nᵢ` would be defined as `−Nᵢ(θ, θ̇) = −∂V/∂θᵢ − β θ̇ᵢ`,
where `β` is the damping coefficient. Other forces acting on the manipulator, such as forces applied
at the end-effector, can also be included by reflecting them to the joints (via the transpose of
the appropriate Jacobian)."

**Formalized.**

* `viscousN V' β`: `N(θ, θ̇) = ∂V/∂θ + β θ̇` for a potential with derivative `V'(θ)` at every `θ`
  (`Lagrangian.gradient`), and `RobotSystem.withViscousFriction`, a robot `(M, C, ·)` with this `N`.
* `RobotSystem.withEndEffectorForce`: an end-effector force `F` reflected to the joints, `−Jᵀ F`
  added to `N`, so that the equations read `M θ̈ + C θ̇ + N = τ + Jᵀ F`
  (`withEndEffectorForce_equations_iff`).
* A consequence the book does not print: with `M` symmetric and the skew property, the energy
  `½ θ̇ᵀ M θ̇ + V(θ)` changes along every motion of the damped robot at the rate `θ̇ · τ − β |θ̇|²`
  (`hasDerivAt_energy_withViscousFriction`), so for `β ≥ 0` and `τ = 0` it does not increase
  (`energy_rate_nonpos`).

Configurations `Fin n → ℝ`; the damping coefficient is one real `β` for every joint, as printed.
Nothing here concerns a physical joint or a friction model beyond the printed linear one.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace Control

variable {n : ℕ}

/-- **Viscous joint friction (MLS printed p. 170):** `N(θ, θ̇) = ∂V/∂θ + β θ̇`, the forces
`−Nᵢ = −∂V/∂θᵢ − β θ̇ᵢ` of a potential `V` with derivative `V'(θ)` and damping coefficient `β`. -/
def viscousN (V' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ) (β : ℝ) :
    (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ :=
  fun θ v => Lagrangian.gradient (V' θ) + β • v

namespace RobotSystem

/-- **A robot with viscous joint friction (MLS printed p. 170):** the inertia and Coriolis matrices
of `R` with `N = ∂V/∂θ + β θ̇`. -/
def withViscousFriction (R : RobotSystem n) (V' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ) (β : ℝ) :
    RobotSystem n where
  M := R.M
  C := R.C
  N := viscousN V' β

/-- **An end-effector force reflected to the joints (MLS printed p. 170, "via the transpose of the
appropriate Jacobian"):** for a Jacobian field `J(θ) ∈ ℝ^{k×n}` and an end-effector force `F`, the
robot with `N − Jᵀ F` in place of `N`. -/
def withEndEffectorForce {k : ℕ} (R : RobotSystem n) (J : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ)
    (F : Fin k → ℝ) : RobotSystem n where
  M := R.M
  C := R.C
  N θ v := R.N θ v - (J θ)ᵀ *ᵥ F

/-- **The end-effector force enters the equations as `Jᵀ F` (MLS printed p. 170):**
`M θ̈ + C θ̇ + (N − Jᵀ F) = τ` exactly when `M θ̈ + C θ̇ + N = τ + Jᵀ F`. -/
theorem withEndEffectorForce_equations_iff {k : ℕ} (R : RobotSystem n)
    (J : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ) (F : Fin k → ℝ) (θ v a τ : Fin n → ℝ) :
    (R.withEndEffectorForce J F).M θ *ᵥ a + (R.withEndEffectorForce J F).C θ v *ᵥ v +
        (R.withEndEffectorForce J F).N θ v = τ ↔
      R.M θ *ᵥ a + R.C θ v *ᵥ v + R.N θ v = τ + (J θ)ᵀ *ᵥ F := by
  simp only [withEndEffectorForce]
  constructor
  · intro h
    rw [← h]
    abel
  · intro h
    rw [← add_sub_assoc, h, add_sub_cancel_right]

/-- **The energy balance of a robot with viscous friction (MLS printed p. 170 with the passivity
remark of p. 172; not printed as a theorem).** With `M(θ)` symmetric for every `θ`, the skew
property of `(M, C)`, `V'(θ)` the derivative of `V` at every `θ`, and a motion `θ` with velocity
`θ'(t)` and acceleration `a` at `t` and an actual derivative `Ṁ` of `s ↦ M(θ(s))`: if
`M θ̈ + C θ̇ + ∂V/∂θ + β θ̇ = τ` at `t`, the energy `½ θ̇ᵀ M θ̇ + V(θ)` has the derivative
`θ̇ · τ − β (θ̇ · θ̇)` at `t`. -/
theorem hasDerivAt_energy_withViscousFriction (R : RobotSystem n) (hM : ∀ q, (R.M q).IsSymm)
    (hskew : R.HasSkewProperty) {V : (Fin n → ℝ) → ℝ} {V' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    (hV : ∀ q, HasFDerivAt V (V' q) q) (β : ℝ) {θ θ' : ℝ → Fin n → ℝ} {a : Fin n → ℝ}
    {Md : Matrix (Fin n) (Fin n) ℝ} {t : ℝ} (hθ : HasDerivAt θ (θ' t) t) (hθ' : HasDerivAt θ' a t)
    (hMd : ∀ i j, HasDerivAt (fun s => R.M (θ s) i j) (Md i j) t) (τ : Fin n → ℝ)
    (hE : (R.withViscousFriction V' β).M (θ t) *ᵥ a +
        (R.withViscousFriction V' β).C (θ t) (θ' t) *ᵥ θ' t +
        (R.withViscousFriction V' β).N (θ t) (θ' t) = τ) :
    HasDerivAt (fun s => Lagrangian.energy R.M V (θ s) (θ' s))
      (θ' t ⬝ᵥ τ - β * (θ' t ⬝ᵥ θ' t)) t := by
  have hMw := Control.hasDerivAt_matrix_mulVec hMd hθ'
  have h1 := Control.hasDerivAt_dotProduct hθ' hMw
  have h2 := (hV (θ t)).comp_hasDerivAt t hθ
  have key := (h1.const_mul (1 / 2 : ℝ)).add h2
  convert key using 1
  · funext s
    simp only [Lagrangian.energy, Pi.add_apply, Function.comp_apply]
  have hMdC : Md = R.C (θ t) (θ' t) + (R.C (θ t) (θ' t))ᵀ := R.deriv_eq_add_transpose hM hskew hθ hMd
  have hs : a ⬝ᵥ (R.M (θ t) *ᵥ θ' t) = θ' t ⬝ᵥ (R.M (θ t) *ᵥ a) :=
    Control.dotProduct_mulVec_comm (hM (θ t)) a (θ' t)
  have hT : θ' t ⬝ᵥ ((R.C (θ t) (θ' t))ᵀ *ᵥ θ' t) = θ' t ⬝ᵥ (R.C (θ t) (θ' t) *ᵥ θ' t) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  have hMa : R.M (θ t) *ᵥ a = τ - R.C (θ t) (θ' t) *ᵥ θ' t -
      (Lagrangian.gradient (V' (θ t)) + β • θ' t) := by
    rw [← hE]
    simp only [withViscousFriction, viscousN]
    abel
  rw [Lagrangian.apply_eq_dotProduct_gradient, hs, hMa, hMdC, Matrix.add_mulVec]
  simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul, hT]
  ring

/-- **With `β ≥ 0` and no applied torque the energy of the damped robot does not increase (MLS
printed p. 170; not printed as a theorem):** the rate `θ̇ · 0 − β (θ̇ · θ̇)` is at most `0`. -/
theorem energy_rate_nonpos {β : ℝ} (hβ : 0 ≤ β) (v : Fin n → ℝ) :
    v ⬝ᵥ (0 : Fin n → ℝ) - β * (v ⬝ᵥ v) ≤ 0 := by
  have h : 0 ≤ v ⬝ᵥ v := dotProduct_self_star_nonneg v
  rw [dotProduct_zero, zero_sub, neg_nonpos]
  exact mul_nonneg hβ h

end RobotSystem
end Control
end RoboLean
