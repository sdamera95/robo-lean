import RoboLean.Control.RobotSystem
import RoboLean.Dynamics.PseudoInverse

/-!
# Control of robot hands: the torques (6.36) and computed torque for (6.21) (MLS §6.5.1)

MLS Chapter 6, §5.1, printed pp. 300–302 (text and renders read this session).

**What MLS states.** For a constrained robot system `M(q) ẍ + C(q, q̇) ẋ + N(q, q̇) = F = G J⁻ᵀ τ`
with `G J⁻ᵀ` surjective, `M(q) > 0` and `Ṁ − 2C` skew (p. 300), `F` is treated as a virtual input:
"Since `G J⁻ᵀ` is surjective, it is always possible to find a set of torques `τ` which realizes this
virtual input" (p. 301); the computed torque controller becomes
`F = M(q)(ẍ_d − K_v ė − K_p e) + C(q, q̇) ẋ + N(q, q̇)`; "Once `F` has been determined, the joint
torques `τ` are chosen so that `G J⁻ᵀ τ = F`. ... The general solution to `G J⁻ᵀ τ = F` has the form
`τ = Jᵀ G⁺ F + Jᵀ f_N` (6.36), where `G⁺ = Gᵀ (G Gᵀ)⁻¹` is the pseudo-inverse of `G` and
`f_N ∈ N(G)`. Since `G f_N = 0`, `f_N` can be chosen arbitrarily without affecting the trajectory
tracking characteristics of the controller."

**Formalized** (sign convention and effective parameters of `CompositeDynamics`):

* (6.36): `graspTorque J G F f_N = Jᵀ (G⁺ F + f_N)` produces `G J⁻ᵀ τ = F` for `J` invertible, `G`
  onto and `G f_N = 0` (`effectiveForce_graspTorque`), every solution has this form
  (`effectiveForce_eq_iff_graspTorque`), and `G J⁻ᵀ` is onto (`effectiveForce_surjective`); the
  actuator part of the contact force is `J⁻ᵀ τ = G⁺ F + f_N` (`inv_transpose_mulVec_graspTorque`).
* Computed torque for (6.21) with the torques (6.36): exponential tracking of the object trajectory
  for every choice of `f_N ∈ N(G)` (`graspTorque_tracking`, any positive definite `M(s)`;
  `effective_graspTorque_tracking`, the effective parameters (6.22) with `M_o` positive definite,
  Lemma 6.1(1)). `M(s)` may depend on the finger coordinates (p. 301: "in this controller `M(q)`
  depends on both `θ` and `x`").
* The hand–object system as a robot `(M, C, N)` on the object coordinates (`handRobot`), for finger
  fields already written in object coordinates (the holonomic case of p. 301, "the dependence on `θ`
  can be removed"): its inertia is positive definite (Lemma 6.1(1), `handRobot_M_posDef`,
  `handRobot_M_posDef_of_surjective`) and it has the skew property (Lemma 6.1(2),
  `handRobot_hasSkewProperty`), so Proposition 4.8 for robots applies to it.

Not formalized: the regulation of internal forces (the friction-cone requirement on `f_N`, the
measured-force loop and its algebraic-loop remark, p. 302), and the hierarchical `attach` and
`control` operations of §5.2 (pp. 302–306). Exact model cancellation is assumed, as in MLS.
-/

noncomputable section

open Matrix Filter Topology Set

namespace RoboLean
namespace Composite

variable {n p : ℕ}

/-! ### The general solution (6.36) of `G J⁻ᵀ τ = F` (MLS p. 301) -/

/-- **The joint torques of MLS eq. (6.36), printed p. 301:** `τ = Jᵀ G⁺ F + Jᵀ f_N`, with
`G⁺ = Gᵀ (G Gᵀ)⁻¹` (`rightPinv`) and an internal force `f_N` (in `N(G)` where used). -/
def graspTorque (J : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin p) (Fin n) ℝ) (F : Fin p → ℝ)
    (fN : Fin n → ℝ) : Fin n → ℝ :=
  Jᵀ *ᵥ (rightPinv G *ᵥ F + fN)

/-- **MLS printed p. 301: the contact force due to the actuators is `G⁺ F + f_N`:** for `J`
invertible, `J⁻ᵀ τ = G⁺ F + f_N` for the torques (6.36). -/
theorem inv_transpose_mulVec_graspTorque {J : Matrix (Fin n) (Fin n) ℝ} (hJ : IsUnit J.det)
    (G : Matrix (Fin p) (Fin n) ℝ) (F : Fin p → ℝ) (fN : Fin n → ℝ) :
    (J⁻¹)ᵀ *ᵥ graspTorque J G F fN = rightPinv G *ᵥ F + fN := by
  rw [graspTorque, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hJ,
    Matrix.transpose_one, Matrix.one_mulVec]

/-- **MLS eq. (6.36), printed p. 301: the torques (6.36) realize the virtual input `F`.** For `J`
invertible, `G` onto and `G f_N = 0`, `G J⁻ᵀ τ = F` ("`f_N` can be chosen arbitrarily without
affecting the trajectory tracking characteristics of the controller"). -/
theorem effectiveForce_graspTorque {J : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin p) (Fin n) ℝ}
    (hJ : IsUnit J.det) (hG : Function.Surjective G.mulVec) (F : Fin p → ℝ) {fN : Fin n → ℝ}
    (hfN : G *ᵥ fN = 0) : effectiveForce J G (graspTorque J G F fN) = F := by
  rw [effectiveForce, ← Matrix.mulVec_mulVec, inv_transpose_mulVec_graspTorque hJ,
    Matrix.mulVec_add, mulVec_rightPinv_mulVec hG, hfN, add_zero]

/-- **MLS eq. (6.36), printed p. 301: "The general solution to `G J⁻ᵀ τ = F` has the form
`τ = Jᵀ G⁺ F + Jᵀ f_N` ... `f_N ∈ N(G)`".** For `J` invertible and `G` onto, `G J⁻ᵀ τ = F` exactly
when `τ = Jᵀ G⁺ F + Jᵀ f_N` for some `f_N` with `G f_N = 0`. -/
theorem effectiveForce_eq_iff_graspTorque {J : Matrix (Fin n) (Fin n) ℝ}
    {G : Matrix (Fin p) (Fin n) ℝ} (hJ : IsUnit J.det) (hG : Function.Surjective G.mulVec)
    (τ : Fin n → ℝ) (F : Fin p → ℝ) :
    effectiveForce J G τ = F ↔ ∃ fN, G *ᵥ fN = 0 ∧ τ = graspTorque J G F fN := by
  constructor
  · intro h
    rw [effectiveForce, ← Matrix.mulVec_mulVec] at h
    obtain ⟨fN, hN, he⟩ := (mulVec_eq_iff_exists_rightPinv hG _ F).mp h
    refine ⟨fN, hN, ?_⟩
    rw [graspTorque, ← he, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul _ hJ, Matrix.transpose_one, Matrix.one_mulVec]
  · rintro ⟨fN, hN, rfl⟩
    exact effectiveForce_graspTorque hJ hG F hN

/-- **MLS printed p. 301: "Since `G J⁻ᵀ` is surjective, it is always possible to find a set of
torques `τ` which realizes this virtual input"**, for `J` invertible and `G` onto. -/
theorem effectiveForce_surjective {J : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin p) (Fin n) ℝ}
    (hJ : IsUnit J.det) (hG : Function.Surjective G.mulVec) :
    Function.Surjective (effectiveForce J G) := fun F =>
  ⟨graspTorque J G F 0, effectiveForce_graspTorque hJ hG F (Matrix.mulVec_zero G)⟩

/-! ### Computed torque for the hand–object system (MLS pp. 300–302) -/

/-- **Computed torque for a constrained robot system with the torques (6.36) (MLS printed pp.
300–302, with Proposition 4.8, p. 192).** For `K_p`, `K_v` symmetric positive definite there are
`m, α > 0`, depending only on the gains, such that: for every desired object trajectory with actual
derivatives, every `t₀ ≥ 0`, every object motion `x` with velocity `x'` and acceleration `x''` at
every `t > t₀` and `(x, x')` continuous on `[t₀, ∞)`, all curves `M(s)` (positive definite), `C(s)`,
`N(s)`, `J(s)` (invertible), `G(s)` (onto) and internal forces `f_N(s) ∈ N(G(s))` for `s > t₀`: if
the equations of motion (6.21) `M ẍ + C ẋ + N = G J⁻ᵀ τ` hold with `τ = Jᵀ G⁺ F + Jᵀ f_N` (6.36) and
`F` the computed torque law of p. 301, then the object tracking error decays exponentially. -/
theorem graspTorque_tracking {Kp Kv : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.PosDef)
    (hKv : Kv.PosDef) :
    ∃ m > 0, ∃ α > 0, ∀ {xd xd' xd'' : ℝ → Fin p → ℝ}, (∀ t, HasDerivAt xd (xd' t) t) →
      (∀ t, HasDerivAt xd' (xd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ (x x' x'' : ℝ → Fin p → ℝ)
      (Mt Ct : ℝ → Matrix (Fin p) (Fin p) ℝ) (Nt : ℝ → Fin p → ℝ)
      (J : ℝ → Matrix (Fin n) (Fin n) ℝ) (G : ℝ → Matrix (Fin p) (Fin n) ℝ)
      (fN : ℝ → Fin n → ℝ),
      ContinuousOn (fun s => (x s, x' s)) (Ici t₀) → (∀ s, t₀ < s → HasDerivAt x (x' s) s) →
      (∀ s, t₀ < s → HasDerivAt x' (x'' s) s) → (∀ s, t₀ < s → (Mt s).PosDef) →
      (∀ s, t₀ < s → IsUnit (J s).det) → (∀ s, t₀ < s → Function.Surjective (G s).mulVec) →
      (∀ s, t₀ < s → G s *ᵥ fN s = 0) →
      (∀ s, t₀ < s → Mt s *ᵥ x'' s + Ct s *ᵥ x' s + Nt s =
        effectiveForce (J s) (G s) (graspTorque (J s) (G s)
          (Control.computedTorqueAlong Kp Kv (Mt s) (Ct s) (Nt s) (xd s) (xd' s) (xd'' s) (x s)
            (x' s)) (fN s))) →
      ∀ t, t₀ ≤ t → ‖(x t - xd t, x' t - xd' t)‖ ≤
        m * Real.exp (-α * (t - t₀)) * ‖(x t₀ - xd t₀, x' t₀ - xd' t₀)‖ := by
  obtain ⟨m, hm, α, hα, htrack⟩ := Control.computedTorque_tracking_along hKp hKv
  refine ⟨m, hm, α, hα, fun hd hd' t₀ ht₀ x x' x'' Mt Ct Nt J G fN hc hx hx' hM hJ hG hfN hE t ht =>
    htrack hd hd' t₀ ht₀ x x' x'' Mt Ct Nt hc hx hx' hM (fun s hs => ?_) t ht⟩
  rw [hE s hs, effectiveForce_graspTorque (hJ s hs) (hG s hs) _ (hfN s hs)]

/-- **MLS pp. 278, 300–302: computed torque for the hand–object system (6.21)–(6.22) with the
torques (6.36), through Lemma 6.1(1).** As `graspTorque_tracking`, with the effective parameters
`M̃ = M_o + G J⁻ᵀ M_f J⁻¹ Gᵀ`, `C̃`, `Ñ` of (6.22) built from object and finger curves `M_o(s)`
(positive definite, p. 277), `M_f(s)` (positive semidefinite), `C_o(s)`, `C_f(s)`, `N_o(s)`,
`N_f(s)` and the rate `Bd(s)` of `J⁻¹ Gᵀ`: the positive definiteness of `M̃(s)` needed by the proof
is Lemma 6.1(1) (`effectiveMass_posDef`). -/
theorem effective_graspTorque_tracking {Kp Kv : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.PosDef)
    (hKv : Kv.PosDef) :
    ∃ m > 0, ∃ α > 0, ∀ {xd xd' xd'' : ℝ → Fin p → ℝ}, (∀ t, HasDerivAt xd (xd' t) t) →
      (∀ t, HasDerivAt xd' (xd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ (x x' x'' : ℝ → Fin p → ℝ)
      (Mo Co : ℝ → Matrix (Fin p) (Fin p) ℝ) (No : ℝ → Fin p → ℝ)
      (Mf Cf J : ℝ → Matrix (Fin n) (Fin n) ℝ) (Nf : ℝ → Fin n → ℝ)
      (G : ℝ → Matrix (Fin p) (Fin n) ℝ) (Bd : ℝ → Matrix (Fin n) (Fin p) ℝ)
      (fN : ℝ → Fin n → ℝ),
      ContinuousOn (fun s => (x s, x' s)) (Ici t₀) → (∀ s, t₀ < s → HasDerivAt x (x' s) s) →
      (∀ s, t₀ < s → HasDerivAt x' (x'' s) s) → (∀ s, t₀ < s → (Mo s).PosDef) →
      (∀ s, t₀ < s → (Mf s).PosSemidef) →
      (∀ s, t₀ < s → IsUnit (J s).det) → (∀ s, t₀ < s → Function.Surjective (G s).mulVec) →
      (∀ s, t₀ < s → G s *ᵥ fN s = 0) →
      (∀ s, t₀ < s →
        effectiveMass (Mo s) (Mf s) (J s) (G s) *ᵥ x'' s +
            effectiveCoriolis (Co s) (Cf s) (Mf s) (J s) (G s) (Bd s) *ᵥ x' s +
            effectiveN (No s) (Nf s) (J s) (G s) =
          effectiveForce (J s) (G s) (graspTorque (J s) (G s)
            (Control.computedTorqueAlong Kp Kv (effectiveMass (Mo s) (Mf s) (J s) (G s))
              (effectiveCoriolis (Co s) (Cf s) (Mf s) (J s) (G s) (Bd s))
              (effectiveN (No s) (Nf s) (J s) (G s)) (xd s) (xd' s) (xd'' s) (x s) (x' s))
            (fN s))) →
      ∀ t, t₀ ≤ t → ‖(x t - xd t, x' t - xd' t)‖ ≤
        m * Real.exp (-α * (t - t₀)) * ‖(x t₀ - xd t₀, x' t₀ - xd' t₀)‖ := by
  obtain ⟨m, hm, α, hα, htrack⟩ := graspTorque_tracking (n := n) hKp hKv
  exact ⟨m, hm, α, hα, fun hd hd' t₀ ht₀ x x' x'' Mo Co No Mf Cf J Nf G Bd fN hc hx hx' hMo hMf
    hJ hG hfN hE t ht =>
    htrack hd hd' t₀ ht₀ x x' x'' (fun s => effectiveMass (Mo s) (Mf s) (J s) (G s))
      (fun s => effectiveCoriolis (Co s) (Cf s) (Mf s) (J s) (G s) (Bd s))
      (fun s => effectiveN (No s) (Nf s) (J s) (G s)) J G fN hc hx hx'
      (fun s hs => effectiveMass_posDef (hMo s hs) (hMf s hs) (J s) (G s)) hJ hG hfN hE t ht⟩

/-! ### The hand–object system as a robot (MLS pp. 278, 300–301) -/

/-- **The hand–object system (6.21)–(6.22) as a robot `(M, C, N)` on the object coordinates (MLS
printed pp. 278, 300–301).** The finger fields `M_f`, `C_f`, `N_f`, the hand Jacobian `J_h` and the
grasp map `G` are given as functions of the object configuration `x` (and velocity `ẋ`), the
holonomic case of p. 301 ("the dependence on `θ` can be removed"); `Bd x v` stands for the rate of
`J_h⁻¹ Gᵀ` along `v` (an actual derivative wherever the skew property is used). Then `M = M̃`,
`C = C̃`, `N = Ñ` of (6.22); the input is `F = G J_h⁻ᵀ τ`. -/
def handRobot (Mo : (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ)
    (Co : (Fin p → ℝ) → (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ)
    (No : (Fin p → ℝ) → (Fin p → ℝ) → Fin p → ℝ) (Mf : (Fin p → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (Cf : (Fin p → ℝ) → (Fin p → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (Nf : (Fin p → ℝ) → (Fin p → ℝ) → Fin n → ℝ) (J : (Fin p → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (G : (Fin p → ℝ) → Matrix (Fin p) (Fin n) ℝ)
    (Bd : (Fin p → ℝ) → (Fin p → ℝ) → Matrix (Fin n) (Fin p) ℝ) : Control.RobotSystem p where
  M x := effectiveMass (Mo x) (Mf x) (J x) (G x)
  C x v := effectiveCoriolis (Co x v) (Cf x v) (Mf x) (J x) (G x) (Bd x v)
  N x v := effectiveN (No x v) (Nf x v) (J x) (G x)

variable {Mo : (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ}
  {Co : (Fin p → ℝ) → (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ}
  {No : (Fin p → ℝ) → (Fin p → ℝ) → Fin p → ℝ} {Mf : (Fin p → ℝ) → Matrix (Fin n) (Fin n) ℝ}
  {Cf : (Fin p → ℝ) → (Fin p → ℝ) → Matrix (Fin n) (Fin n) ℝ}
  {Nf : (Fin p → ℝ) → (Fin p → ℝ) → Fin n → ℝ} {J : (Fin p → ℝ) → Matrix (Fin n) (Fin n) ℝ}
  {G : (Fin p → ℝ) → Matrix (Fin p) (Fin n) ℝ}
  {Bd : (Fin p → ℝ) → (Fin p → ℝ) → Matrix (Fin n) (Fin p) ℝ}

/-- **MLS Lemma 6.1(1), p. 279, for the hand robot, from the object (p. 277, `M_o(x) > 0`):** with
`M_o(x)` positive definite and `M_f(x)` positive semidefinite at every `x`, the robot's inertia is
positive definite everywhere (any `J_h`, `G`). -/
theorem handRobot_M_posDef (hMo : ∀ x, (Mo x).PosDef) (hMf : ∀ x, (Mf x).PosSemidef)
    (x : Fin p → ℝ) :
    ((handRobot Mo Co No Mf Cf Nf J G Bd).M x).PosDef :=
  effectiveMass_posDef (hMo x) (hMf x) (J x) (G x)

/-- **MLS Lemma 6.1(1), p. 279, for the hand robot, the book's route (force-closure makes `G`
onto):** with `M_f(x)` positive definite, `M_o(x)` positive semidefinite (possibly `0`), `J_h(x)`
invertible and `G(x)` onto at `x`, the robot's inertia is positive definite at `x`. -/
theorem handRobot_M_posDef_of_surjective {x : Fin p → ℝ} (hMo : (Mo x).PosSemidef)
    (hMf : (Mf x).PosDef) (hJ : IsUnit (J x).det) (hG : Function.Surjective (G x).mulVec) :
    ((handRobot Mo Co No Mf Cf Nf J G Bd).M x).PosDef :=
  effectiveMass_posDef_of_surjective hMo hMf hJ hG

/-- **MLS Lemma 6.1(2), p. 279, for the hand robot: it has the skew property (MLS p. 300, "These
properties hold for all of the systems given in this chapter").** Hypotheses: the entries of `M_o`
and `M_f` are differentiable functions of the object coordinates, `M_f(x)` is symmetric, the object
and finger pairs `(M_o, C_o)`, `(M_f, C_f)` have `Ṁ − 2C` skew along motions (the "usual structural
properties", p. 283), and `Bd(x(t), x')` is the actual derivative of `s ↦ J_h(x(s))⁻¹ G(x(s))ᵀ` at
`t` along every motion. -/
theorem handRobot_hasSkewProperty (hMo : ∀ i j, Differentiable ℝ fun y => Mo y i j)
    (hMf : ∀ i j, Differentiable ℝ fun y => Mf y i j) (hMf_symm : ∀ y, (Mf y)ᵀ = Mf y)
    (hso : Control.SkewAlongMotions Mo Co) (hsf : Control.SkewAlongMotions Mf Cf)
    (hB : ∀ {x : ℝ → Fin p → ℝ} {x' : Fin p → ℝ} {t : ℝ}, HasDerivAt x x' t →
      ∀ i j, HasDerivAt (fun s => ((J (x s))⁻¹ * (G (x s))ᵀ) i j) (Bd (x t) x' i j) t) :
    (handRobot Mo Co No Mf Cf Nf J G Bd).HasSkewProperty := by
  intro x x' t Md hx hMd
  have hMo' : ∀ i j, HasDerivAt (fun s => Mo (x s) i j)
      (fderiv ℝ (fun y => Mo y i j) (x t) x') t := fun i j =>
    ((hMo i j) (x t)).hasFDerivAt.comp_hasDerivAt t hx
  have hMf' : ∀ i j, HasDerivAt (fun s => Mf (x s) i j)
      (fderiv ℝ (fun y => Mf y i j) (x t) x') t := fun i j =>
    ((hMf i j) (x t)).hasFDerivAt.comp_hasDerivAt t hx
  exact skew_deriv_effectiveMass_sub_two_effectiveCoriolis (Mo := fun s => Mo (x s))
    (Mf := fun s => Mf (x s)) (J := fun s => J (x s)) (G := fun s => G (x s))
    (Mod := Matrix.of fun i j => fderiv ℝ (fun y => Mo y i j) (x t) x')
    (Mfd := Matrix.of fun i j => fderiv ℝ (fun y => Mf y i j) (x t) x') hMo' hMf' (hB hx)
    (hMf_symm (x t)) (hso hx hMo') (hsf hx hMf') hMd

end Composite
end RoboLean
