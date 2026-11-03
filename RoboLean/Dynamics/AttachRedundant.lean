import RoboLean.Control.RobotAttach
import RoboLean.Dynamics.RedundantDynamics

/-!
# `attach` with redundant fingers: internal-motion variables and the pseudo-inverse (MLS p. 305)

MLS Chapter 6, printed p. 305: the `attach` formulas assume "that `J` is invertible for the purposes
of exposition"; "the attach operation can be used to ... add variables parameterizing the internal
motion of a redundant robot". For redundant fingers (§3.1, pp. 285–290) the hand Jacobian
`J_h ∈ ℝ^{m×n}` has more columns than rows; the book augments it to `J̄_h = [J_h; K_h]` with internal
velocities `v_N = K_h θ̇` (p. 289) and, for `K` with orthonormal rows perpendicular to those of `J`,
`J̄⁻¹ = [J⁺ Kᵀ]` with the right pseudo-inverse `J⁺ = Jᵀ (J Jᵀ)⁻¹` (p. 287).

**Formalized.** `redundantAttach`: the constraint data of an `attach` whose payload coordinates
`w = (x, y)` are the object configuration and the internal-motion variables, with `J = J̄_h` and
`G = Ḡ` (`Ḡᵀ = [[Gᵀ, 0], [0, I]]`, p. 289) from the library's augmentation
(`Dynamics/RedundantDynamics`). Then:

* `J̄_h` is invertible for `J_h` and `K_h` onto with `J_h K_hᵀ = 0` (`isUnit_det_redundantAttach_J`),
  so every theorem about `attach` applies, in particular its equations as the constrained equations
  of fingers and payload (`redundantAttach_equations_iff`);
* the finger velocity of the attached robot is `J̄_h⁻¹ Ḡᵀ ẇ = J_h⁺ Gᵀ ẋ + K_hᵀ ẏ` for `K_h` with
  orthonormal rows (`redundantAttach_fingerVelocity`), the minimum-norm solution of `J_h θ̇ = Gᵀ ẋ`
  plus the internal motion: this is the redundant `J` "through the pseudo-inverse";
* that velocity satisfies the grasp constraint `J_h θ̇ = Gᵀ ẋ` and `K_h θ̇ = ẏ`
  (`redundantAttach_fingerVelocity_constraint`).

**Hypotheses MLS does not state**, explicit: `J_h(w)` and `K_h(w)` onto, `J_h K_hᵀ = 0`, and for the
pseudo-inverse form `K_h K_hᵀ = I`; the finger configuration `σ(w)` and the rate `Bd` are data, as
in `AttachConstraint`. Nothing here concerns a physical hand.
-/

noncomputable section

open Matrix
open RoboLean.Composite RoboLean.Constrained

namespace RoboLean
namespace Control

variable {n m p r P : ℕ}

/-- **The `attach` constraint data of redundant fingers with internal-motion variables (MLS printed
p. 305, "add variables parameterizing the internal motion of a redundant robot", with p. 289):**
payload coordinates `w = (x, y)` relabeled by `ew : Fin p ⊕ Fin r ≃ Fin P`, `J = J̄_h = [J_h; K_h]`
(rows relabeled by `ea`) and `G = Ḡ` with `Ḡᵀ = [[Gᵀ, 0], [0, I]]`. -/
def redundantAttach (ea : Fin m ⊕ Fin r ≃ Fin n) (ew : Fin p ⊕ Fin r ≃ Fin P)
    (σ : (Fin P → ℝ) → Fin n → ℝ) (Jh : (Fin P → ℝ) → Matrix (Fin m) (Fin n) ℝ)
    (Kh : (Fin P → ℝ) → Matrix (Fin r) (Fin n) ℝ) (G : (Fin P → ℝ) → Matrix (Fin p) (Fin m) ℝ)
    (Bd : (Fin P → ℝ) → (Fin P → ℝ) → Matrix (Fin n) (Fin P) ℝ) : AttachConstraint n P where
  σ := σ
  J w := augmentedJacobian ea (Jh w) (Kh w)
  G w := augmentedGrasp ew ea (G w)
  Bd := Bd

variable (ea : Fin m ⊕ Fin r ≃ Fin n) (ew : Fin p ⊕ Fin r ≃ Fin P) (σ : (Fin P → ℝ) → Fin n → ℝ)
  (Jh : (Fin P → ℝ) → Matrix (Fin m) (Fin n) ℝ) (Kh : (Fin P → ℝ) → Matrix (Fin r) (Fin n) ℝ)
  (G : (Fin P → ℝ) → Matrix (Fin p) (Fin m) ℝ)
  (Bd : (Fin P → ℝ) → (Fin P → ℝ) → Matrix (Fin n) (Fin P) ℝ)

/-- **The augmented Jacobian of the redundant `attach` is invertible (MLS printed pp. 286–287, "By
definition, `J̄` is invertible"),** for `J_h(w)`, `K_h(w)` onto and `J_h(w) K_h(w)ᵀ = 0`. -/
theorem isUnit_det_redundantAttach_J {w : Fin P → ℝ} (hJ : Function.Surjective (Jh w).mulVec)
    (hK : Function.Surjective (Kh w).mulVec) (hJK : Jh w * (Kh w)ᵀ = 0) :
    IsUnit ((redundantAttach ea ew σ Jh Kh G Bd).J w).det :=
  isUnit_det_augmentedJacobian ea hJ hK hJK

/-- **The finger velocity of the redundant `attach` through the pseudo-inverse (MLS printed p. 287,
`J̄⁻¹ = [J⁺ Kᵀ]`, with p. 305):** for `J_h(w)` onto, `J_h(w) K_h(w)ᵀ = 0` and `K_h(w) K_h(w)ᵀ = I`,
`J̄_h⁻¹ Ḡᵀ ẇ = J_h⁺ Gᵀ ẋ + K_hᵀ ẏ` with `J_h⁺ = J_hᵀ (J_h J_hᵀ)⁻¹`. -/
theorem redundantAttach_fingerVelocity {w : Fin P → ℝ} (hJ : Function.Surjective (Jh w).mulVec)
    (hJK : Jh w * (Kh w)ᵀ = 0) (hKK : Kh w * (Kh w)ᵀ = 1) (v : Fin P → ℝ) :
    (redundantAttach ea ew σ Jh Kh G Bd).fingerVelocity w v =
      rightPinv (Jh w) *ᵥ ((G w)ᵀ *ᵥ splitFst ew v) + (Kh w)ᵀ *ᵥ splitSnd ew v := by
  have hKJ : Kh w * rightPinv (Jh w) = 0 := by
    have h := congrArg Matrix.transpose hJK
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at h
    rw [rightPinv, ← Matrix.mul_assoc, h, Matrix.zero_mul]
  have hK : Function.Surjective (Kh w).mulVec := fun b =>
    ⟨(Kh w)ᵀ *ᵥ b, by rw [Matrix.mulVec_mulVec, hKK, Matrix.one_mulVec]⟩
  have hu := isUnit_det_augmentedJacobian ea hJ hK hJK
  set u := rightPinv (Jh w) *ᵥ ((G w)ᵀ *ᵥ splitFst ew v) + (Kh w)ᵀ *ᵥ splitSnd ew v
  have hc : augmentedJacobian ea (Jh w) (Kh w) *ᵥ u = (augmentedGrasp ew ea (G w))ᵀ *ᵥ v := by
    rw [augmented_constraint_iff]
    constructor
    · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, mul_rightPinv hJ, Matrix.one_mulVec,
        Matrix.mulVec_mulVec, hJK, Matrix.zero_mulVec, add_zero]
    · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hKJ, Matrix.zero_mulVec, zero_add,
        Matrix.mulVec_mulVec, hKK, Matrix.one_mulVec]
  change ((augmentedJacobian ea (Jh w) (Kh w))⁻¹ * (augmentedGrasp ew ea (G w))ᵀ) *ᵥ v = u
  rw [← Matrix.mulVec_mulVec, ← hc, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mulVec]

/-- **The finger velocity of the redundant `attach` satisfies the grasp constraint and moves the
internal variables (MLS printed p. 289):** for `J_h(w)`, `K_h(w)` onto and `J_h(w) K_h(w)ᵀ = 0`,
`θ̇ = J̄_h⁻¹ Ḡᵀ ẇ` satisfies `J_h θ̇ = Gᵀ ẋ` and `K_h θ̇ = ẏ`. -/
theorem redundantAttach_fingerVelocity_constraint {w : Fin P → ℝ}
    (hJ : Function.Surjective (Jh w).mulVec) (hK : Function.Surjective (Kh w).mulVec)
    (hJK : Jh w * (Kh w)ᵀ = 0) (v : Fin P → ℝ) :
    Jh w *ᵥ (redundantAttach ea ew σ Jh Kh G Bd).fingerVelocity w v =
        (G w)ᵀ *ᵥ splitFst ew v ∧
      Kh w *ᵥ (redundantAttach ea ew σ Jh Kh G Bd).fingerVelocity w v = splitSnd ew v := by
  have hu := isUnit_det_augmentedJacobian ea hJ hK hJK
  rw [← augmented_constraint_iff]
  change augmentedJacobian ea (Jh w) (Kh w) *ᵥ
      (((augmentedJacobian ea (Jh w) (Kh w))⁻¹ * (augmentedGrasp ew ea (G w))ᵀ) *ᵥ v) = _
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

/-- **The redundant attached robot's equations are the constrained equations of fingers and payload
(MLS printed p. 305 with (6.24), p. 280, and p. 289),** for `J_h(w)`, `K_h(w)` onto and
`J_h(w) K_h(w)ᵀ = 0`: `RobotSystem.attach_equations_iff` with the invertibility of `J̄_h` discharged. -/
theorem redundantAttach_equations_iff (F : RobotSystem n) (Pl : RobotSystem P) {w v a : Fin P → ℝ}
    (hJ : Function.Surjective (Jh w).mulVec) (hK : Function.Surjective (Kh w).mulVec)
    (hJK : Jh w * (Kh w)ᵀ = 0) (τ : Fin n → ℝ) :
    (∃ lam : Fin n → ℝ,
      F.M ((redundantAttach ea ew σ Jh Kh G Bd).σ w) *ᵥ
            (redundantAttach ea ew σ Jh Kh G Bd).fingerAcceleration w v a +
          F.C ((redundantAttach ea ew σ Jh Kh G Bd).σ w)
              ((redundantAttach ea ew σ Jh Kh G Bd).fingerVelocity w v) *ᵥ
            (redundantAttach ea ew σ Jh Kh G Bd).fingerVelocity w v +
          F.N ((redundantAttach ea ew σ Jh Kh G Bd).σ w)
            ((redundantAttach ea ew σ Jh Kh G Bd).fingerVelocity w v) +
          ((redundantAttach ea ew σ Jh Kh G Bd).J w)ᵀ *ᵥ lam = τ ∧
        Pl.M w *ᵥ a + Pl.C w v *ᵥ v + Pl.N w v =
          (redundantAttach ea ew σ Jh Kh G Bd).G w *ᵥ lam) ↔
      (F.attach Pl (redundantAttach ea ew σ Jh Kh G Bd)).M w *ᵥ a +
          (F.attach Pl (redundantAttach ea ew σ Jh Kh G Bd)).C w v *ᵥ v +
          (F.attach Pl (redundantAttach ea ew σ Jh Kh G Bd)).N w v =
        effectiveForce ((redundantAttach ea ew σ Jh Kh G Bd).J w)
          ((redundantAttach ea ew σ Jh Kh G Bd).G w) τ :=
  RobotSystem.attach_equations_iff F Pl _ (isUnit_det_redundantAttach_J ea ew σ Jh Kh G Bd hJ hK hJK) τ

end Control
end RoboLean
