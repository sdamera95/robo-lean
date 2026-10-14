import RoboLean.Dynamics.PseudoInverse
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Redundant manipulators and redundant grasps (MLS Chapter 6, §3.1, eqs. (6.29)–(6.31))

MLS Chapter 6, §3.1, printed pp. 285–290 (renders of pp. 287–289 inspected this session).

**What MLS states.** For a manipulator Jacobian `J(θ) ∈ ℝ^{p×n}` of full row rank, "we define a
matrix `K(θ) ∈ ℝ^{(n−p)×n}` whose rows span the null space of `J(θ)`" and the internal motion
`v_N = K θ̇`, so that `(ẋ, v_N) = [J; K] θ̇ =: J̄ θ̇`; "By definition, `J̄` is invertible and it
follows from our previous derivation that `M̃ (ẍ, v̇_N) + C̃ (ẋ, v_N) + Ñ = J̄⁻ᵀ τ`" with
`M̃ = J̄⁻ᵀ M J̄⁻¹`, `C̃ = J̄⁻ᵀ (C J̄⁻¹ + M (d/dt) J̄⁻¹)`, `Ñ = N_o + J̄⁻ᵀ N_f` (p. 287). "If we
choose `K` such that its rows are orthonormal and also perpendicular to the rows of `J`, then
`J̄⁻¹ = [J⁺ Kᵀ]` where `J⁺ = Jᵀ (J Jᵀ)⁻¹`." For a redundant grasp (p. 289) the constraint
`J_h θ̇ = Gᵀ ẋ` is augmented to `[J_h; K_h] θ̇ = [[Gᵀ, 0], [0, I]] (ẋ, v_N)`, i.e.
`J̄_h θ̇ = Ḡᵀ (ẋ, v_N)`, and the dynamics are (6.30) `M̃ (ẍ, v̇_N) + C̃ (ẋ, v_N) = Ḡ J̄_h⁻ᵀ τ`,
`M̃ = Ḡ J̄_h⁻ᵀ M J̄_h⁻¹ Ḡᵀ`, `C̃ = Ḡ J̄_h⁻ᵀ (C J̄_h⁻¹ Ḡᵀ + M (d/dt)(J̄_h⁻¹ Ḡᵀ))`. The quasistatic
forces are (6.31) `τ = [J_hᵀ K_hᵀ] (f_c, f_N)`, `F^b_{po} = G f_c` (p. 290).

**Formalized** (carriers of `CompositeDynamics`; the row blocks of `J̄` and the columns of `Ḡ` are
relabeled by equivalences `Fin p ⊕ Fin r ≃ Fin n`, so that `J̄` is a square matrix on `Fin n`):

* `augmentedJacobian e J K` (`J̄`), with `J̄ θ̇ = (J θ̇, K θ̇)`; `J̄` is invertible for `J` and `K`
  onto (full row rank) and `J Kᵀ = 0` (`isUnit_det_augmentedJacobian`), and then the rows of `K`
  span `N(J)` (`mulVec_eq_zero_iff_exists`); for `J Kᵀ = 0` and `K Kᵀ = I`, `J̄⁻¹ = [J⁺ Kᵀ]`
  (`inv_augmentedJacobian`). The book's "rows span the null space of `J`" is stated through these
  hypotheses (with `r` rows, `K` onto and `J Kᵀ = 0`).
* (6.29) as the instance `G = I`, `M_o = 0` of (6.21)–(6.22) (`redundant_dynamics_iff`: the joint
  equations hold exactly when the end-effector equations hold), with the structural properties of
  Lemma 6.1 (`effectiveMass_one_posDef`; `skew_deriv_redundant`); a smooth `K` enters only through
  an actual derivative of `J̄⁻¹` (`hasDerivAt_inv_augmentedJacobian` computes it from rates of `J`
  and `K`).
* The redundant grasp: `augmentedGrasp` (`Ḡ`), the augmented constraint
  (`augmented_constraint_iff`), the constraint `[J_h −Gᵀ]` with a rectangular `J_h`
  (`graspPfaffian`), and (6.30) derived from the Lagrange–d'Alembert equations
  (`lagrangeDAlembertAt_graspPfaffian_iff_effective`), with the object terms that the printed (6.30)
  omits (`M_o`, `C_o` and `N_o` on the `ẋ` rows; with them zero it is the printed form).
* (6.31): `τ = J̄_hᵀ (f_c, f_N) = J_hᵀ f_c + K_hᵀ f_N` and `Ḡ (f_c, f_N) = (G f_c, f_N)`
  (`augmentedJacobian_transpose_mulVec`, `augmentedGrasp_mulVec`), the power balance
  `τ ⬝ θ̇ = (G f_c) ⬝ ẋ + f_N ⬝ v_N` (`dotProduct_augmented_power`), and with `f_N = 0` the usual
  relation `τ = J_hᵀ f_c` (5.16).

Hypotheses the book does not print, all explicit: `J` and `K` onto (the book's "full row rank" and
"rows span"); `J̄` invertible along the motion near `t`; actual derivatives of `J̄⁻¹` (respectively
`J̄_h⁻¹ Ḡᵀ`) and of `(ẋ, v_N)` at `t`; symmetric inertia fields with derivative data as in
`CompositeDynamics`. Nonmanipulable grasps (§3.2, (6.32)–(6.33)) are not formalized.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Composite

open Constrained

variable {p r n : ℕ}

/-! ### The augmented Jacobian `J̄ = [J; K]` (MLS p. 287) -/

/-- **The augmented Jacobian `J̄ = [J; K]` of MLS printed p. 287**, `J ∈ ℝ^{p×n}`, `K ∈ ℝ^{r×n}`
(the book's `r = n − p`), with the rows `(ẋ, v_N)` relabeled by `e : Fin p ⊕ Fin r ≃ Fin n`, so that
`J̄` is a square matrix on `Fin n`. -/
def augmentedJacobian (e : Fin p ⊕ Fin r ≃ Fin n) (J : Matrix (Fin p) (Fin n) ℝ)
    (K : Matrix (Fin r) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.fromRows J K).submatrix e.symm id

/-- **MLS printed p. 287: `(ẋ, v_N) = [J; K] θ̇ = J̄ θ̇`**, in the relabeled coordinates
(`Constrained.splitJoin`). -/
theorem augmentedJacobian_mulVec (e : Fin p ⊕ Fin r ≃ Fin n) (J : Matrix (Fin p) (Fin n) ℝ)
    (K : Matrix (Fin r) (Fin n) ℝ) (v : Fin n → ℝ) :
    augmentedJacobian e J K *ᵥ v = splitJoin e (J *ᵥ v) (K *ᵥ v) := by
  funext i
  obtain ⟨s, rfl⟩ := e.surjective i
  rcases s with a | b <;> simp [augmentedJacobian, splitJoin, Matrix.mulVec, dotProduct]

/-- **MLS eq. (6.31), printed p. 290: `[J_hᵀ K_hᵀ] (f_c, f_N) = J_hᵀ f_c + K_hᵀ f_N`**, i.e. the
transpose of `J̄` applied to the relabeled forces. -/
theorem augmentedJacobian_transpose_mulVec (e : Fin p ⊕ Fin r ≃ Fin n)
    (J : Matrix (Fin p) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ) (f : Fin n → ℝ) :
    (augmentedJacobian e J K)ᵀ *ᵥ f = Jᵀ *ᵥ splitFst e f + Kᵀ *ᵥ splitSnd e f := by
  funext j
  simp only [Matrix.mulVec, Pi.add_apply]
  rw [dotProduct_split e]
  simp [splitFst, splitSnd, augmentedJacobian, dotProduct, Matrix.transpose_apply]

/-- **MLS printed pp. 286–287: "By definition, `J̄` is invertible"**, for `J` of full row rank
(onto), `K` of full row rank (onto) and the rows of `K` perpendicular to those of `J` (`J Kᵀ = 0`):
the rows of `K` are then a basis of `N(J)` (`mulVec_eq_zero_iff_exists`). -/
theorem isUnit_det_augmentedJacobian (e : Fin p ⊕ Fin r ≃ Fin n) {J : Matrix (Fin p) (Fin n) ℝ}
    {K : Matrix (Fin r) (Fin n) ℝ} (hJ : Function.Surjective J.mulVec)
    (hK : Function.Surjective K.mulVec) (hJK : J * Kᵀ = 0) :
    IsUnit (augmentedJacobian e J K).det := by
  have h0 : ∀ f, (augmentedJacobian e J K)ᵀ *ᵥ f = 0 → f = 0 := by
    intro f hf
    rw [augmentedJacobian_transpose_mulVec] at hf
    have hu : IsUnit (J * Jᵀ) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr ((isUnit_det_mul_transpose_iff_surjective J).mpr hJ)
    have ha : (J * Jᵀ) *ᵥ splitFst e f = 0 := by
      have h1 := congrArg (J *ᵥ ·) hf
      simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, hJK, Matrix.zero_mulVec, add_zero,
        Matrix.mulVec_zero] at h1
      exact h1
    have ha0 : splitFst e f = 0 :=
      Matrix.mulVec_injective_iff_isUnit.mpr hu (ha.trans (Matrix.mulVec_zero _).symm)
    rw [ha0, Matrix.mulVec_zero, zero_add] at hf
    have hb0 : splitSnd e f = 0 :=
      transpose_mulVec_injective_of_surjective hK (hf.trans (Matrix.mulVec_zero _).symm)
    rw [← splitJoin_splitFst_splitSnd e f, ha0, hb0]
    funext j
    simp [splitJoin]
  have hinj : Function.Injective (augmentedJacobian e J K)ᵀ.mulVec := by
    intro x y hxy
    have := h0 (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])
    exact sub_eq_zero.mp this
  rw [← Matrix.det_transpose, ← Matrix.isUnit_iff_isUnit_det]
  exact Matrix.mulVec_injective_iff_isUnit.mp hinj

/-- **MLS printed p. 286: "`K(θ)` whose rows span the null space of `J(θ)`"**: under the hypotheses
of `isUnit_det_augmentedJacobian`, `J v = 0` exactly when `v = Kᵀ c` for some `c`. -/
theorem mulVec_eq_zero_iff_exists (e : Fin p ⊕ Fin r ≃ Fin n) {J : Matrix (Fin p) (Fin n) ℝ}
    {K : Matrix (Fin r) (Fin n) ℝ} (hJ : Function.Surjective J.mulVec)
    (hK : Function.Surjective K.mulVec) (hJK : J * Kᵀ = 0) (v : Fin n → ℝ) :
    J *ᵥ v = 0 ↔ ∃ c, v = Kᵀ *ᵥ c := by
  constructor
  · intro hv
    have hu : IsUnit (K * Kᵀ).det := (isUnit_det_mul_transpose_iff_surjective K).mpr hK
    refine ⟨(K * Kᵀ)⁻¹ *ᵥ (K *ᵥ v), ?_⟩
    have hJ0 : J *ᵥ (v - Kᵀ *ᵥ ((K * Kᵀ)⁻¹ *ᵥ (K *ᵥ v))) = 0 := by
      rw [Matrix.mulVec_sub, hv, Matrix.mulVec_mulVec, hJK, Matrix.zero_mulVec, sub_zero]
    have hK0 : K *ᵥ (v - Kᵀ *ᵥ ((K * Kᵀ)⁻¹ *ᵥ (K *ᵥ v))) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec, sub_self]
    have hJb : augmentedJacobian e J K *ᵥ (v - Kᵀ *ᵥ ((K * Kᵀ)⁻¹ *ᵥ (K *ᵥ v))) =
        augmentedJacobian e J K *ᵥ 0 := by
      rw [augmentedJacobian_mulVec, hJ0, hK0, Matrix.mulVec_zero]
      funext j
      simp [splitJoin]
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_augmentedJacobian e hJ hK hJK))
    exact sub_eq_zero.mp (hinj hJb)
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_mulVec, hJK, Matrix.zero_mulVec]

/-- **MLS printed p. 287: "If we choose `K` such that its rows are orthonormal and also
perpendicular to the rows of `J`, then `J̄⁻¹ = [J⁺ Kᵀ]` where `J⁺ = Jᵀ (J Jᵀ)⁻¹`"**, for `J` onto,
`J Kᵀ = 0` and `K Kᵀ = I`, with the columns of `[J⁺ Kᵀ]` relabeled by `e`. -/
theorem inv_augmentedJacobian (e : Fin p ⊕ Fin r ≃ Fin n) {J : Matrix (Fin p) (Fin n) ℝ}
    {K : Matrix (Fin r) (Fin n) ℝ} (hJ : Function.Surjective J.mulVec) (hJK : J * Kᵀ = 0)
    (hKK : K * Kᵀ = 1) :
    (augmentedJacobian e J K)⁻¹ = (Matrix.fromCols (rightPinv J) Kᵀ).submatrix id e.symm := by
  have hKJ : K * Jᵀ = 0 := by
    have h := congrArg Matrix.transpose hJK
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at h
  apply Matrix.inv_eq_right_inv
  rw [augmentedJacobian, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
    Matrix.fromRows_mul_fromCols, mul_rightPinv hJ, hJK, hKK, rightPinv, ← Matrix.mul_assoc, hKJ,
    Matrix.zero_mul, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

/-- **A smooth `K` (MLS printed p. 287, `(d/dt) J̄⁻¹`):** if the entries of `s ↦ J(s)` and
`s ↦ K(s)` have the derivatives `J'`, `K'` at `t` and `J̄(t)` is invertible, the entries of
`s ↦ J̄(s)⁻¹` have the derivative `−J̄⁻¹ [J'; K'] J̄⁻¹` at `t`. -/
theorem hasDerivAt_inv_augmentedJacobian (e : Fin p ⊕ Fin r ≃ Fin n)
    {J : ℝ → Matrix (Fin p) (Fin n) ℝ} {K : ℝ → Matrix (Fin r) (Fin n) ℝ}
    {J' : Matrix (Fin p) (Fin n) ℝ} {K' : Matrix (Fin r) (Fin n) ℝ} {t : ℝ}
    (hJ : ∀ i j, HasDerivAt (fun s => J s i j) (J' i j) t)
    (hK : ∀ i j, HasDerivAt (fun s => K s i j) (K' i j) t)
    (hu : IsUnit (augmentedJacobian e (J t) (K t)).det) (i j : Fin n) :
    HasDerivAt (fun s => (augmentedJacobian e (J s) (K s))⁻¹ i j)
      ((-((augmentedJacobian e (J t) (K t))⁻¹ * augmentedJacobian e J' K' *
        (augmentedJacobian e (J t) (K t))⁻¹)) i j) t := by
  refine Control.hasDerivAt_matrix_inv (fun i j => ?_) hu i j
  simp only [augmentedJacobian, Matrix.submatrix_apply, id]
  rcases e.symm i with a | b
  · simpa using hJ a j
  · simpa using hK b j

/-! ### Dynamics of a redundant manipulator, eq. (6.29) (MLS pp. 287–288) -/

/-- **MLS printed p. 287 and eq. (6.29), p. 288: the dynamics of a redundant manipulator in the
coordinates `(ẋ, v_N)`**, as the instance `G = I`, `M_o = C_o = N_o = 0` of (6.21)–(6.22). Along a
motion with `J̄(s) θ̇(s) = w(s)` (the book's `(ẋ, v_N)`) and `J̄(s)` invertible for `s` near `t`,
`Bd` the derivative of `s ↦ J̄(s)⁻¹` at `t` and `θ̇`, `w` with derivatives `θ̈`, `ẇ` at `t`:
`M θ̈ + C θ̇ + N = τ` exactly when `M̃ ẇ + C̃ w + Ñ = J̄⁻ᵀ τ` with `M̃ = J̄⁻ᵀ M J̄⁻¹`,
`C̃ = J̄⁻ᵀ (C J̄⁻¹ + M (d/dt) J̄⁻¹)`, `Ñ = J̄⁻ᵀ N`. -/
theorem redundant_dynamics_iff {Jb : ℝ → Matrix (Fin n) (Fin n) ℝ} {θ' w : ℝ → Fin n → ℝ}
    {θ'' w' : Fin n → ℝ} {Bd : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hc : ∀ᶠ s in 𝓝 t, Jb s *ᵥ θ' s = w s) (hJ : ∀ᶠ s in 𝓝 t, IsUnit (Jb s).det)
    (hB : ∀ i j, HasDerivAt (fun s => (Jb s)⁻¹ i j) (Bd i j) t) (hθ' : HasDerivAt θ' θ'' t)
    (hw : HasDerivAt w w' t) (M C : Matrix (Fin n) (Fin n) ℝ) (N τ : Fin n → ℝ) :
    M *ᵥ θ'' + C *ᵥ θ' t + N = τ ↔
      effectiveMass 0 M (Jb t) 1 *ᵥ w' + effectiveCoriolis 0 C M (Jb t) 1 Bd *ᵥ w t +
          effectiveN 0 N (Jb t) 1 = effectiveForce (Jb t) 1 τ := by
  have hc' : ∀ᶠ s in 𝓝 t, Jb s *ᵥ θ' s = (1 : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ w s := by
    filter_upwards [hc] with s hs
    rw [Matrix.transpose_one, Matrix.one_mulVec, hs]
  have hB' : ∀ i j, HasDerivAt (fun s => ((Jb s)⁻¹ * (1 : Matrix (Fin n) (Fin n) ℝ)ᵀ) i j)
      (Bd i j) t := by
    intro i j
    simpa only [Matrix.transpose_one, Matrix.mul_one] using hB i j
  obtain ⟨hv, ha⟩ := velocity_acceleration_eq hc' hJ hB' hθ' hw
  have hu : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ) * ((Jb t)⁻¹)ᵀ) := by
    rw [Matrix.one_mul, Matrix.isUnit_transpose, Matrix.isUnit_iff_isUnit_det]
    exact Matrix.isUnit_nonsing_inv_det _ hJ.self_of_nhds
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hu
  rw [← effective_dynamics_eq 0 0 0 M C (Jb t) N 1 Bd hv ha, effectiveForce]
  simp only [Matrix.zero_mulVec, add_zero, zero_add]
  exact hinj.eq_iff.symm

/-- **MLS eq. (6.29), p. 288, with Lemma 6.1(2), p. 279: the end-effector dynamics of a redundant
manipulator keep the skew property.** If the entries of `s ↦ M(s)` and `s ↦ J̄(s)⁻¹` have the
derivatives `Ṁ`, `Bd` at `t`, `M(t)` is symmetric and `Ṁ − 2C` is skew-symmetric, then every actual
derivative of `s ↦ J̄(s)⁻ᵀ M(s) J̄(s)⁻¹` at `t` minus `2C̃` is skew-symmetric. -/
theorem skew_deriv_redundant {M Jb : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {Md C Bd : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hM : ∀ i j, HasDerivAt (fun s => M s i j) (Md i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => (Jb s)⁻¹ i j) (Bd i j) t) (hsymm : (M t)ᵀ = M t)
    (hs : (Md - (2 : ℝ) • C)ᵀ = -(Md - (2 : ℝ) • C)) {Mtd : Matrix (Fin n) (Fin n) ℝ}
    (hMt : ∀ i j, HasDerivAt (fun s => effectiveMass 0 (M s) (Jb s) 1 i j) (Mtd i j) t) :
    (Mtd - (2 : ℝ) • effectiveCoriolis 0 C (M t) (Jb t) 1 Bd)ᵀ =
      -(Mtd - (2 : ℝ) • effectiveCoriolis 0 C (M t) (Jb t) 1 Bd) := by
  have hB' : ∀ i j, HasDerivAt (fun s => ((Jb s)⁻¹ * (1 : Matrix (Fin n) (Fin n) ℝ)ᵀ) i j)
      (Bd i j) t := by
    intro i j
    simpa only [Matrix.transpose_one, Matrix.mul_one] using hB i j
  exact skew_deriv_effectiveMass_sub_two_effectiveCoriolis (Mo := fun _ => 0) (Mod := 0)
    (Co := 0) (fun i j => hasDerivAt_const t _) hM hB' hsymm (by simp) hs hMt

/-! ### Redundant grasps, eq. (6.30) (MLS p. 289) -/

variable {m P N : ℕ}

/-- **The augmented grasp map `Ḡ` of MLS printed p. 289, `Ḡᵀ = [[Gᵀ, 0], [0, I]]`**, for a grasp map
`G ∈ ℝ^{p×m}`: rows `(ẋ, v_N)` relabeled by `ew : Fin p ⊕ Fin r ≃ Fin P`, columns `(f_c, f_N)`
relabeled by `ea : Fin m ⊕ Fin r ≃ Fin n` (the rows of `J̄_h = [J_h; K_h]`). -/
def augmentedGrasp (ew : Fin p ⊕ Fin r ≃ Fin P) (ea : Fin m ⊕ Fin r ≃ Fin n)
    (G : Matrix (Fin p) (Fin m) ℝ) : Matrix (Fin P) (Fin n) ℝ :=
  (Matrix.fromBlocks G 0 0 1).submatrix ew.symm ea.symm

/-- **MLS eq. (6.31), printed p. 290: `Ḡ (f_c, f_N) = (G f_c, f_N)`**, the object wrench
`F^b_{po} = G f_c` and the internal-motion forces `f_N`. -/
theorem augmentedGrasp_mulVec (ew : Fin p ⊕ Fin r ≃ Fin P) (ea : Fin m ⊕ Fin r ≃ Fin n)
    (G : Matrix (Fin p) (Fin m) ℝ) (f : Fin n → ℝ) :
    augmentedGrasp ew ea G *ᵥ f = splitJoin ew (G *ᵥ splitFst ea f) (splitSnd ea f) := by
  rw [augmentedGrasp, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, Matrix.fromBlocks_mulVec]
  funext j
  obtain ⟨s, rfl⟩ := ew.surjective j
  rcases s with a | b
  · simp [splitJoin, Function.comp_def]
    rfl
  · simp [splitJoin, splitSnd, Function.comp_def]

/-- **MLS printed p. 289: `Ḡᵀ (ẋ, v_N) = (Gᵀ ẋ, v_N)`.** -/
theorem augmentedGrasp_transpose_mulVec (ew : Fin p ⊕ Fin r ≃ Fin P)
    (ea : Fin m ⊕ Fin r ≃ Fin n) (G : Matrix (Fin p) (Fin m) ℝ) (w : Fin P → ℝ) :
    (augmentedGrasp ew ea G)ᵀ *ᵥ w = splitJoin ea (Gᵀ *ᵥ splitFst ew w) (splitSnd ew w) := by
  rw [augmentedGrasp, Matrix.transpose_submatrix, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_mulVec]
  funext j
  obtain ⟨s, rfl⟩ := ea.surjective j
  rcases s with a | b
  · simp [splitJoin, Function.comp_def]
    rfl
  · simp [splitJoin, splitSnd, Function.comp_def]

/-- Two relabeled pairs agree exactly when both parts agree (MLS p. 272). -/
private theorem splitJoin_eq_splitJoin_iff {a b c : ℕ} (e : Fin a ⊕ Fin b ≃ Fin c)
    (u₁ v₁ : Fin a → ℝ) (u₂ v₂ : Fin b → ℝ) :
    splitJoin e u₁ u₂ = splitJoin e v₁ v₂ ↔ u₁ = v₁ ∧ u₂ = v₂ := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (splitFst e) h, by simpa using congrArg (splitSnd e) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **MLS printed p. 289: the augmented grasp constraint
`[J_h; K_h] θ̇ = [[Gᵀ, 0], [0, I]] (ẋ, v_N)` is the grasp constraint `J_h θ̇ = Gᵀ ẋ` together with
`v_N = K_h θ̇`.** -/
theorem augmented_constraint_iff (ew : Fin p ⊕ Fin r ≃ Fin P) (ea : Fin m ⊕ Fin r ≃ Fin n)
    (Jh : Matrix (Fin m) (Fin n) ℝ) (Kh : Matrix (Fin r) (Fin n) ℝ) (G : Matrix (Fin p) (Fin m) ℝ)
    (θ' : Fin n → ℝ) (w : Fin P → ℝ) :
    augmentedJacobian ea Jh Kh *ᵥ θ' = (augmentedGrasp ew ea G)ᵀ *ᵥ w ↔
      Jh *ᵥ θ' = Gᵀ *ᵥ splitFst ew w ∧ Kh *ᵥ θ' = splitSnd ew w := by
  rw [augmentedJacobian_mulVec, augmentedGrasp_transpose_mulVec, splitJoin_eq_splitJoin_iff]

/-- **The grasp constraint (6.18) with a rectangular hand Jacobian (MLS printed p. 289,
`J_h θ̇ = Gᵀ ẋ` with `N(J_h) ≠ 0`), as a Pfaffian constraint `A = [J_h −Gᵀ]` (sign of p. 267)**:
`J_h(q) ∈ ℝ^{m×n}`, `G(q) ∈ ℝ^{p×m}`, columns of `q` relabeled by `e` as in `handPfaffian` (which is
the case `m = n`). -/
def graspPfaffian (e : Fin p ⊕ Fin n ≃ Fin N) (Jh : (Fin N → ℝ) → Matrix (Fin m) (Fin n) ℝ)
    (G : (Fin N → ℝ) → Matrix (Fin p) (Fin m) ℝ) : (Fin N → ℝ) → Matrix (Fin m) (Fin N) ℝ :=
  fun q => Matrix.of fun i j => Sum.elim (fun a => -(G q)ᵀ i a) (fun b => Jh q i b) (e.symm j)

/-- **MLS p. 267: with a square hand Jacobian, `graspPfaffian` is `handPfaffian`.** -/
theorem graspPfaffian_eq_handPfaffian (e : Fin p ⊕ Fin n ≃ Fin N)
    (Jh : (Fin N → ℝ) → Matrix (Fin n) (Fin n) ℝ) (G : (Fin N → ℝ) → Matrix (Fin p) (Fin n) ℝ) :
    graspPfaffian e Jh G = handPfaffian e Jh G :=
  rfl

/-- The `x` block of `[J_h −Gᵀ]` is `−Gᵀ` (MLS p. 267). -/
private theorem colsFst_graspPfaffian (e : Fin p ⊕ Fin n ≃ Fin N)
    (Jh : (Fin N → ℝ) → Matrix (Fin m) (Fin n) ℝ) (G : (Fin N → ℝ) → Matrix (Fin p) (Fin m) ℝ)
    (q : Fin N → ℝ) : colsFst (graspPfaffian e Jh G q) e = -(G q)ᵀ := by
  ext i a
  simp [colsFst, graspPfaffian]

/-- The `θ` block of `[J_h −Gᵀ]` is `J_h` (MLS p. 267). -/
private theorem colsSnd_graspPfaffian (e : Fin p ⊕ Fin n ≃ Fin N)
    (Jh : (Fin N → ℝ) → Matrix (Fin m) (Fin n) ℝ) (G : (Fin N → ℝ) → Matrix (Fin p) (Fin m) ℝ)
    (q : Fin N → ℝ) : colsSnd (graspPfaffian e Jh G q) e = Jh q := by
  ext i b
  simp [colsSnd, graspPfaffian]

/-- **MLS printed p. 289: the redundant grasp constraint `[J_h −Gᵀ] q̇ = 0` is `J_h θ̇ = Gᵀ ẋ`.** -/
theorem pfaffianAt_graspPfaffian_iff (e : Fin p ⊕ Fin n ≃ Fin N)
    (Jh : (Fin N → ℝ) → Matrix (Fin m) (Fin n) ℝ) (G : (Fin N → ℝ) → Matrix (Fin p) (Fin m) ℝ)
    (q v : Fin N → ℝ) :
    PfaffianAt (graspPfaffian e Jh G) q v ↔ Jh q *ᵥ splitSnd e v = (G q)ᵀ *ᵥ splitFst e v := by
  unfold PfaffianAt
  rw [mulVec_split _ e, colsFst_graspPfaffian, colsSnd_graspPfaffian, Matrix.neg_mulVec,
    neg_add_eq_sub, sub_eq_zero]

/-- The relabeled parts of a motion have the relabeled parts of its derivative. -/
private theorem hasDerivAt_splitFst_of {a b c : ℕ} (e : Fin a ⊕ Fin b ≃ Fin c)
    {q : ℝ → Fin c → ℝ} {q' : Fin c → ℝ} {s : ℝ} (h : HasDerivAt q q' s) :
    HasDerivAt (fun s => splitFst e (q s)) (splitFst e q') s :=
  hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mp h (e (Sum.inl i))

/-- The relabeled parts of a motion have the relabeled parts of its derivative. -/
private theorem hasDerivAt_splitSnd_of {a b c : ℕ} (e : Fin a ⊕ Fin b ≃ Fin c)
    {q : ℝ → Fin c → ℝ} {q' : Fin c → ℝ} {s : ℝ} (h : HasDerivAt q q' s) :
    HasDerivAt (fun s => splitSnd e (q s)) (splitSnd e q') s :=
  hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mp h (e (Sum.inr i))

/-- Relabeled parts commute with subtraction. -/
private theorem splitFst_sub_of {a b c : ℕ} (e : Fin a ⊕ Fin b ≃ Fin c) (u v : Fin c → ℝ) :
    splitFst e (u - v) = splitFst e u - splitFst e v := rfl

/-- Relabeled parts commute with subtraction. -/
private theorem splitSnd_sub_of {a b c : ℕ} (e : Fin a ⊕ Fin b ≃ Fin c) (u v : Fin c → ℝ) :
    splitSnd e (u - v) = splitSnd e u - splitSnd e v := rfl

/-- **The virtual displacements of the redundant grasp constraint (MLS p. 289).** If `A δq = 0` is
`J_h δθ = Gᵀ δx` and `J̄_h` is invertible, the virtual displacements are `δq = (u_x, J̄_h⁻¹ Ḡᵀ u)`
for `u ∈ ℝᴾ`, so `F` does no virtual work exactly when `(F_x, 0) + Ḡ J̄_h⁻ᵀ F_θ = 0`. -/
private theorem doesNoVirtualWork_graspPfaffian_iff (e : Fin p ⊕ Fin n ≃ Fin N)
    (ea : Fin m ⊕ Fin r ≃ Fin n) (ew : Fin p ⊕ Fin r ≃ Fin P) {Jh : Matrix (Fin m) (Fin n) ℝ}
    {Kh : Matrix (Fin r) (Fin n) ℝ} {G : Matrix (Fin p) (Fin m) ℝ} {A : Matrix (Fin m) (Fin N) ℝ}
    (hA : ∀ v, A *ᵥ v = 0 ↔ Jh *ᵥ splitSnd e v = Gᵀ *ᵥ splitFst e v)
    (hJ : IsUnit (augmentedJacobian ea Jh Kh).det) (F : Fin N → ℝ) :
    DoesNoVirtualWork A F ↔ splitJoin ew (splitFst e F) 0 +
      (augmentedGrasp ew ea G * ((augmentedJacobian ea Jh Kh)⁻¹)ᵀ) *ᵥ splitSnd e F = 0 := by
  set Jb := augmentedJacobian ea Jh Kh
  set Gb := augmentedGrasp ew ea G
  set y := splitJoin ew (splitFst e F) 0 + (Gb * (Jb⁻¹)ᵀ) *ᵥ splitSnd e F
  have hS : ∀ u, F ⬝ᵥ splitJoin e (splitFst ew u) ((Jb⁻¹ * Gbᵀ) *ᵥ u) = y ⬝ᵥ u := by
    intro u
    rw [dotProduct_split e, splitFst_splitJoin, splitSnd_splitJoin, add_dotProduct,
      dotProduct_split ew (splitJoin ew _ 0), splitFst_splitJoin, splitSnd_splitJoin,
      zero_dotProduct, add_zero, ← transpose_inv_mul_transpose, Matrix.mulVec_transpose,
      ← Matrix.dotProduct_mulVec]
  have hrep : ∀ δq, A *ᵥ δq = 0 ↔
      ∃ u, δq = splitJoin e (splitFst ew u) ((Jb⁻¹ * Gbᵀ) *ᵥ u) := by
    intro δq
    constructor
    · intro h
      refine ⟨splitJoin ew (splitFst e δq) (Kh *ᵥ splitSnd e δq), ?_⟩
      have h1 : Jb *ᵥ splitSnd e δq =
          Gbᵀ *ᵥ splitJoin ew (splitFst e δq) (Kh *ᵥ splitSnd e δq) :=
        (augmented_constraint_iff ew ea Jh Kh G _ _).mpr
          ⟨by rw [splitFst_splitJoin]; exact (hA δq).mp h, by rw [splitSnd_splitJoin]⟩
      have h2 : splitSnd e δq =
          (Jb⁻¹ * Gbᵀ) *ᵥ splitJoin ew (splitFst e δq) (Kh *ᵥ splitSnd e δq) := by
        rw [← Matrix.mulVec_mulVec, ← h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hJ,
          Matrix.one_mulVec]
      rw [splitFst_splitJoin, ← h2, splitJoin_splitFst_splitSnd]
    · rintro ⟨u, rfl⟩
      rw [hA, splitFst_splitJoin, splitSnd_splitJoin]
      have h1 : Jb *ᵥ ((Jb⁻¹ * Gbᵀ) *ᵥ u) = Gbᵀ *ᵥ u := by
        rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ,
          Matrix.one_mul]
      exact ((augmented_constraint_iff ew ea Jh Kh G _ u).mp h1).1
  constructor
  · intro h
    have h0 := h _ ((hrep _).mpr ⟨y, rfl⟩)
    rw [hS] at h0
    exact dotProduct_self_eq_zero.mp h0
  · intro hy δq hδ
    obtain ⟨u, rfl⟩ := (hrep δq).mp hδ
    rw [hS, hy, zero_dotProduct]

/-- **MLS eq. (6.30), printed p. 289, derived from the Lagrange–d'Alembert equations ("The
Lagrange-d'Alembert formalism lets us treat this case without difficulty", p. 287).** For mechanical
finger and object Lagrangians (6.19) with symmetric inertia fields and Fréchet derivative data at
`θ(t)`, `x(t)`, along a motion `q` with velocity `q'` near `t` and acceleration `q''` at `t`, with
the redundant grasp constraint `J_h θ̇ = Gᵀ ẋ` on a neighborhood of `t`, the augmented velocities
`w(s) = (ẋ(s), K_h θ̇(s))` near `t` with derivative `ẇ` at `t`, `J̄_h(s)` invertible near `t` and
`Bd` the derivative of `s ↦ J̄_h(s)⁻¹ Ḡ(s)ᵀ` at `t`: the Lagrange–d'Alembert equations with the
force `(τ, 0)` hold at `t` exactly when `M̃ ẇ + C̃ w + Ñ = Ḡ J̄_h⁻ᵀ τ`, with `M̃`, `C̃`, `Ñ` of
(6.22) for `J̄_h`, `Ḡ` and the object terms `diag(M_o, 0)`, `diag(C_o, 0)`, `(N_o, 0)` on `(ẋ, v_N)`
(MLS prints (6.30) without them). -/
theorem lagrangeDAlembertAt_graspPfaffian_iff_effective (e : Fin p ⊕ Fin n ≃ Fin N)
    (ea : Fin m ⊕ Fin r ≃ Fin n) (ew : Fin p ⊕ Fin r ≃ Fin P)
    {Mo : (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ} {Mo' : Fin p → Fin p → ((Fin p → ℝ) →L[ℝ] ℝ)}
    {Vo : (Fin p → ℝ) → ℝ} {Vo' : (Fin p → ℝ) →L[ℝ] ℝ}
    {Mf : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {Mf' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)}
    {Vf : (Fin n → ℝ) → ℝ} {Vf' : (Fin n → ℝ) →L[ℝ] ℝ}
    {Jh : (Fin N → ℝ) → Matrix (Fin m) (Fin n) ℝ} {Kh : (Fin N → ℝ) → Matrix (Fin r) (Fin n) ℝ}
    {G : (Fin N → ℝ) → Matrix (Fin p) (Fin m) ℝ} {q q' : ℝ → Fin N → ℝ} {q'' : Fin N → ℝ}
    {w : ℝ → Fin P → ℝ} {w' : Fin P → ℝ} {Bd : Matrix (Fin n) (Fin P) ℝ} {t : ℝ}
    (hMo_symm : ∀ y, (Mo y).IsSymm) (hMf_symm : ∀ y, (Mf y).IsSymm)
    (hMo : ∀ i j, HasFDerivAt (fun y => Mo y i j) (Mo' i j) (splitFst e (q t)))
    (hVo : HasFDerivAt Vo Vo' (splitFst e (q t)))
    (hMf : ∀ i j, HasFDerivAt (fun y => Mf y i j) (Mf' i j) (splitSnd e (q t)))
    (hVf : HasFDerivAt Vf Vf' (splitSnd e (q t))) (hq : ∀ᶠ s in 𝓝 t, HasDerivAt q (q' s) s)
    (hq' : HasDerivAt q' q'' t)
    (hc : ∀ᶠ s in 𝓝 t, PfaffianAt (graspPfaffian e Jh G) (q s) (q' s))
    (hw : ∀ᶠ s in 𝓝 t, w s = splitJoin ew (splitFst e (q' s)) (Kh (q s) *ᵥ splitSnd e (q' s)))
    (hw' : HasDerivAt w w' t)
    (hJ : ∀ᶠ s in 𝓝 t, IsUnit (augmentedJacobian ea (Jh (q s)) (Kh (q s))).det)
    (hB : ∀ i j, HasDerivAt (fun s => ((augmentedJacobian ea (Jh (q s)) (Kh (q s)))⁻¹ *
      (augmentedGrasp ew ea (G (q s)))ᵀ) i j) (Bd i j) t) (τ : Fin n → ℝ) :
    LagrangeDAlembertAt (lagrangian e (Lagrangian.mechanical Mo Vo) (Lagrangian.mechanical Mf Vf))
        (graspPfaffian e Jh G) q (handForce e τ) t ↔
      effectiveMass (blockMatrix ew (Mo (splitFst e (q t))) 0) (Mf (splitSnd e (q t)))
            (augmentedJacobian ea (Jh (q t)) (Kh (q t))) (augmentedGrasp ew ea (G (q t))) *ᵥ w' +
          effectiveCoriolis
              (blockMatrix ew
                (Christoffel.coriolisMatrix (Christoffel.partials Mo') (splitFst e (q' t))) 0)
              (Christoffel.coriolisMatrix (Christoffel.partials Mf') (splitSnd e (q' t)))
              (Mf (splitSnd e (q t))) (augmentedJacobian ea (Jh (q t)) (Kh (q t)))
              (augmentedGrasp ew ea (G (q t))) Bd *ᵥ w t +
          effectiveN (splitJoin ew (Lagrangian.gradient Vo') 0) (Lagrangian.gradient Vf')
            (augmentedJacobian ea (Jh (q t)) (Kh (q t))) (augmentedGrasp ew ea (G (q t))) =
        effectiveForce (augmentedJacobian ea (Jh (q t)) (Kh (q t)))
          (augmentedGrasp ew ea (G (q t))) τ := by
  set Ro := Mo (splitFst e (q t)) *ᵥ splitFst e q'' +
    Christoffel.coriolisMatrix (Christoffel.partials Mo') (splitFst e (q' t)) *ᵥ
      splitFst e (q' t) + Lagrangian.gradient Vo'
  set Rf := Mf (splitSnd e (q t)) *ᵥ splitSnd e q'' +
    Christoffel.coriolisMatrix (Christoffel.partials Mf') (splitSnd e (q' t)) *ᵥ
      splitSnd e (q' t) + Lagrangian.gradient Vf'
  have hxq : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => splitFst e (q s)) (splitFst e (q' s)) s := by
    filter_upwards [hq] with s hs
    exact hasDerivAt_splitFst_of e hs
  have hθq : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => splitSnd e (q s)) (splitSnd e (q' s)) s := by
    filter_upwards [hq] with s hs
    exact hasDerivAt_splitSnd_of e hs
  have hRo := lagrangeEquationsAt_mechanical_inertial hMo_symm hMo hVo hxq
    (hasDerivAt_splitFst_of e hq')
  have hRf := lagrangeEquationsAt_mechanical_inertial hMf_symm hMf hVf hθq
    (hasDerivAt_splitSnd_of e hq')
  have hR : Lagrangian.LagrangeEquationsAt
      (lagrangian e (Lagrangian.mechanical Mo Vo) (Lagrangian.mechanical Mf Vf)) q
      (splitJoin e Ro Rf) t :=
    (lagrangeEquationsAt_lagrangian_iff e _ _ hq _).mpr
      ⟨by rwa [splitFst_splitJoin], by rwa [splitSnd_splitJoin]⟩
  have hc' : ∀ᶠ s in 𝓝 t, augmentedJacobian ea (Jh (q s)) (Kh (q s)) *ᵥ splitSnd e (q' s) =
      (augmentedGrasp ew ea (G (q s)))ᵀ *ᵥ w s := by
    filter_upwards [hc, hw] with s hs hws
    rw [hws]
    refine (augmented_constraint_iff ew ea _ _ _ _ _).mpr ⟨?_, ?_⟩
    · rw [splitFst_splitJoin]
      exact (pfaffianAt_graspPfaffian_iff e Jh G _ _).mp hs
    · rw [splitSnd_splitJoin]
  obtain ⟨hv, ha⟩ := velocity_acceleration_eq hc' hJ hB (hasDerivAt_splitSnd_of e hq') hw'
  have hw0 : splitFst ew (w t) = splitFst e (q' t) := by
    rw [hw.self_of_nhds, splitFst_splitJoin]
  have hw1 : splitFst ew w' = splitFst e q'' := by
    have h2 : HasDerivAt (fun s => splitFst ew (w s)) (splitFst e q'') t := by
      refine (hasDerivAt_splitFst_of e hq').congr_of_eventuallyEq ?_
      filter_upwards [hw] with s hs
      rw [hs, splitFst_splitJoin]
    exact (hasDerivAt_splitFst_of ew hw').unique h2
  have hkey : blockMatrix ew (Mo (splitFst e (q t))) 0 *ᵥ w' +
      blockMatrix ew
        (Christoffel.coriolisMatrix (Christoffel.partials Mo') (splitFst e (q' t))) 0 *ᵥ w t +
      splitJoin ew (Lagrangian.gradient Vo') 0 = splitJoin ew Ro 0 := by
    rw [blockMatrix_mulVec, blockMatrix_mulVec, hw0, hw1]
    funext j
    obtain ⟨s, rfl⟩ := ew.surjective j
    rcases s with a | b <;> simp [splitJoin, Ro]
  rw [lagrangeDAlembertAt_iff_of_lagrangeEquationsAt hR,
    doesNoVirtualWork_graspPfaffian_iff e ea ew
      (fun v => pfaffianAt_graspPfaffian_iff e Jh G (q t) v) hJ.self_of_nhds,
    ← effective_dynamics_eq _ _ _ _ _ _ _ _ _ hv ha, hkey, effectiveForce, splitFst_sub_of,
    splitSnd_sub_of, splitFst_splitJoin, splitSnd_splitJoin, handForce, splitFst_splitJoin,
    splitSnd_splitJoin, sub_zero, Matrix.mulVec_sub, ← add_sub_assoc, sub_eq_zero]

/-! ### The quasistatic forces of a redundant grasp, eq. (6.31) (MLS p. 290) -/

/-- **MLS eq. (6.31), printed p. 290: the power balance of the quasistatic forces.** If
`J_h θ̇ = Gᵀ ẋ` and `v_N = K_h θ̇`, the torques `τ = [J_hᵀ K_hᵀ] (f_c, f_N)` deliver the power
`τ ⬝ θ̇ = (G f_c) ⬝ ẋ + f_N ⬝ v_N`: the object wrench `F^b_{po} = G f_c` against the object velocity
and `f_N` against the internal motion ("The forces `f_N` parameterize the forces which correspond to
internal motions `v_N`"). -/
theorem dotProduct_augmented_power (ea : Fin m ⊕ Fin r ≃ Fin n) {Jh : Matrix (Fin m) (Fin n) ℝ}
    (Kh : Matrix (Fin r) (Fin n) ℝ) {G : Matrix (Fin p) (Fin m) ℝ} {θ' : Fin n → ℝ}
    {x' : Fin p → ℝ} (hc : Jh *ᵥ θ' = Gᵀ *ᵥ x') (f : Fin n → ℝ) :
    ((augmentedJacobian ea Jh Kh)ᵀ *ᵥ f) ⬝ᵥ θ' =
      (G *ᵥ splitFst ea f) ⬝ᵥ x' + splitSnd ea f ⬝ᵥ (Kh *ᵥ θ') := by
  rw [augmentedJacobian_transpose_mulVec, add_dotProduct, Matrix.mulVec_transpose,
    Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, hc,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- **MLS printed p. 290: "If these forces are chosen to be zero, then we retrieve the usual force
relationships between joint torques and object wrenches"**: with `f_N = 0`,
`[J_hᵀ K_hᵀ] (f_c, 0) = J_hᵀ f_c` (MLS eq. (5.16), p. 238). -/
theorem augmentedJacobian_transpose_mulVec_zero (ea : Fin m ⊕ Fin r ≃ Fin n)
    (Jh : Matrix (Fin m) (Fin n) ℝ) (Kh : Matrix (Fin r) (Fin n) ℝ) (fc : Fin m → ℝ) :
    (augmentedJacobian ea Jh Kh)ᵀ *ᵥ splitJoin ea fc 0 = Jhᵀ *ᵥ fc := by
  rw [augmentedJacobian_transpose_mulVec, splitFst_splitJoin, splitSnd_splitJoin,
    Matrix.mulVec_zero, add_zero]

end Composite
end RoboLean
