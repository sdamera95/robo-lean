import RoboLean.Dynamics.LeftPseudoInverse
import RoboLean.Dynamics.RedundantDynamics

/-!
# Nonmanipulable grasps: eq. (6.33) derived from the constraint (6.32)

MLS Chapter 6, §3.2, printed pp. 290–291.

**What MLS states.** For a grasp with constraint `J_h θ̇ = Gᵀ ẋ` whose hand Jacobian is "full column
rank" (p. 290) but not full row rank, the allowable object velocities are
`W(θ, x) = {ẋ ∈ ℝᵖ : ∃ θ̇, J_h θ̇ = Gᵀ ẋ}`; with `H(θ, x) ∈ ℝ^{p×l}` "whose columns span `W(θ, x)`"
the constraints are (6.32) `J_h θ̇ = Gᵀ H w`, `ẋ = H w`; with `Ḡᵀ := Gᵀ H` and the left
pseudo-inverse `J_h⁺ = (J_hᵀ J_h)⁻¹ J_hᵀ` "the resulting dynamics are given by" (6.33)
`M̃ ẇ + C̃ w + Ñ = F`, printed with `M̃ = M_o + Ḡ J_h⁺ᵀ M_f J_h⁺ Ḡᵀ`,
`C̃ = C_o + Ḡ J_h⁺ᵀ (C_f J_h⁺ Ḡᵀ + M_f (d/dt)(J_h⁺ Ḡᵀ))`, `Ñ = N_o + Ḡ J_h⁺ᵀ N_f`, `F = G J̄_h⁺ᵀ τ`.
The book gives no derivation.

**Formalized: (6.33) as a consequence of (6.32) and the Lagrange–d'Alembert equations.** The
composite Lagrangian (6.19) with the Pfaffian constraint `[J_h −Gᵀ]` of a rectangular `J_h`
(the library's `graspPfaffian`, MLS p. 289) and the joint torques `(τ, 0)` satisfies the
Lagrange–d'Alembert equations at `t` exactly when `M̃ ẇ + C̃ w + Ñ = F` holds with the derived parameters

`M̃ = Hᵀ M_o H + Ḡ J_h⁺ᵀ M_f J_h⁺ Ḡᵀ`, `C̃ = Hᵀ (C_o H + M_o Ḣ) + Ḡ J_h⁺ᵀ (C_f J_h⁺ Ḡᵀ + M_f Ẏ)`,
`Ñ = Hᵀ N_o + Ḡ J_h⁺ᵀ N_f`, `F = Ḡ J_h⁺ᵀ τ`, with `Ḡ = Hᵀ G` and `Ẏ = (d/dt)(J_h⁺ Ḡᵀ)`

(`lagrangeDAlembertAt_graspPfaffian_iff_reduced`). The key step is that the virtual displacements
of `[J_h −Gᵀ]` are exactly `δx = H δw`, `δθ = J_h⁺ Ḡᵀ δw`
(`doesNoVirtualWork_graspPfaffian_iff_reduced`).

**Corrected printing.** The printed object terms `M_o`, `C_o`, `N_o` are `p`-dimensional while
`M̃`, `C̃`, `Ñ` act on `w ∈ ℝˡ`; the derivation gives `Hᵀ M_o H`, `Hᵀ (C_o H + M_o Ḣ)` and `Hᵀ N_o`,
and the printed force `G J̄_h⁺ᵀ τ` is `Ḡ J_h⁺ᵀ τ`. With `H = I` and an invertible `J_h` the derived
parameters are those of (6.22) (`reducedMass_one` and its companions), which is the printed
display read with `l = p`.

**Also formalized.** The allowable velocities `W` as a submodule and the spanning hypothesis on `H`
(`SpansAllowable`); the velocity and acceleration of a motion obeying (6.32)
(`velocity_acceleration_eq_reduced`); `M̃` symmetric, positive definite for `M_o` positive definite
and `H` injective (the book's `H` has `l` columns spanning the `l`-dimensional `W`); and
`M̃˙ − 2C̃` skew at one instant from the skew symmetry of the finger and object pieces.

**Hypotheses the book does not print, all explicit:** `J_h` injective along the motion near `t`
(stated by the book on p. 290); the constraint (6.32) on a neighborhood of `t` with an actual
derivative of `w`, of `H` along the motion and of `J_h⁺ Ḡᵀ` along the motion; the spanning
hypothesis at `t`; symmetric inertia fields. Existence of `H` with constant `l` and its smoothness
("We assume that `W(θ, x)` has constant dimension `l > 0` and that `W` varies smoothly") are not
constructed: `H` is data. Friction-cone conditions (p. 291) are not formalized.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Composite

open Constrained

variable {m n p l : ℕ}

/-! ### Allowable velocities and the basis `H` (MLS p. 291) -/

/-- **The allowable object velocities (MLS printed p. 291):**
`W(θ, x) = {ẋ ∈ ℝᵖ : ∃ θ̇ with J_h θ̇ = Gᵀ ẋ}`, as the preimage under `Gᵀ` of the range of `J_h`. -/
def allowableVelocities (Jh : Matrix (Fin m) (Fin n) ℝ) (G : Matrix (Fin p) (Fin m) ℝ) :
    Submodule ℝ (Fin p → ℝ) :=
  (LinearMap.range (Matrix.mulVecLin Jh)).comap (Matrix.mulVecLin Gᵀ)

/-- **Membership in `W(θ, x)` (MLS printed p. 291).** -/
theorem mem_allowableVelocities (Jh : Matrix (Fin m) (Fin n) ℝ) (G : Matrix (Fin p) (Fin m) ℝ)
    (v : Fin p → ℝ) : v ∈ allowableVelocities Jh G ↔ ∃ θ', Jh *ᵥ θ' = Gᵀ *ᵥ v := by
  simp [allowableVelocities, LinearMap.mem_range, Matrix.mulVec_transpose]

/-- **The columns of `H` span `W(θ, x)` (MLS printed p. 291, "Choosing a matrix `H(θ, x) ∈ ℝ^{p×l}`
whose columns span `W(θ, x)`").** -/
def SpansAllowable (H : Matrix (Fin p) (Fin l) ℝ) (Jh : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin p) (Fin m) ℝ) : Prop :=
  LinearMap.range (Matrix.mulVecLin H) = allowableVelocities Jh G

/-- **`Ḡ` with `Ḡᵀ := Gᵀ H` (MLS printed p. 291):** `Ḡ = Hᵀ G`. -/
def barG (G : Matrix (Fin p) (Fin m) ℝ) (H : Matrix (Fin p) (Fin l) ℝ) : Matrix (Fin l) (Fin m) ℝ :=
  Hᵀ * G

/-- **`Ḡᵀ = Gᵀ H` (MLS printed p. 291).** -/
theorem barG_transpose (G : Matrix (Fin p) (Fin m) ℝ) (H : Matrix (Fin p) (Fin l) ℝ) :
    (barG G H)ᵀ = Gᵀ * H := by
  rw [barG, Matrix.transpose_mul, Matrix.transpose_transpose]

/-! ### The parameters of (6.33) as derived (MLS p. 291, corrected printing) -/

/-- **MLS eq. (6.33), p. 291, the inertia, as derived:** `M̃ = Hᵀ M_o H + Ḡ J_h⁺ᵀ M_f J_h⁺ Ḡᵀ`
(the book prints `M_o` for `Hᵀ M_o H`; corrected printing). -/
def reducedMass (Mo : Matrix (Fin p) (Fin p) ℝ) (Mf : Matrix (Fin n) (Fin n) ℝ)
    (Jh : Matrix (Fin m) (Fin n) ℝ) (G : Matrix (Fin p) (Fin m) ℝ) (H : Matrix (Fin p) (Fin l) ℝ) :
    Matrix (Fin l) (Fin l) ℝ :=
  Hᵀ * Mo * H + barG G H * (leftPinv Jh)ᵀ * Mf * leftPinv Jh * (barG G H)ᵀ

/-- **MLS eq. (6.33), p. 291, the Coriolis matrix, as derived:**
`C̃ = Hᵀ (C_o H + M_o Ḣ) + Ḡ J_h⁺ᵀ (C_f J_h⁺ Ḡᵀ + M_f Ẏ)` with `Ḣ = Hd` and
`Ẏ = (d/dt)(J_h⁺ Ḡᵀ) = Bd` explicit arguments (the book prints `C_o` for `Hᵀ (C_o H + M_o Ḣ)`;
corrected printing). -/
def reducedCoriolis (Co Mo : Matrix (Fin p) (Fin p) ℝ) (Cf Mf : Matrix (Fin n) (Fin n) ℝ)
    (Jh : Matrix (Fin m) (Fin n) ℝ) (G : Matrix (Fin p) (Fin m) ℝ) (H Hd : Matrix (Fin p) (Fin l) ℝ)
    (Bd : Matrix (Fin n) (Fin l) ℝ) : Matrix (Fin l) (Fin l) ℝ :=
  Hᵀ * (Co * H + Mo * Hd) + barG G H * (leftPinv Jh)ᵀ * (Cf * (leftPinv Jh * (barG G H)ᵀ) + Mf * Bd)

/-- **MLS eq. (6.33), p. 291, the remaining forces, as derived:** `Ñ = Hᵀ N_o + Ḡ J_h⁺ᵀ N_f` (the
book prints `N_o` for `Hᵀ N_o`; corrected printing). -/
def reducedN (No : Fin p → ℝ) (Nf : Fin n → ℝ) (Jh : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin p) (Fin m) ℝ) (H : Matrix (Fin p) (Fin l) ℝ) : Fin l → ℝ :=
  Hᵀ *ᵥ No + (barG G H * (leftPinv Jh)ᵀ) *ᵥ Nf

/-- **MLS eq. (6.33), p. 291, the generalized force, as derived:** `F = Ḡ J_h⁺ᵀ τ` (printed
`G J̄_h⁺ᵀ τ`; corrected printing). -/
def reducedForce (Jh : Matrix (Fin m) (Fin n) ℝ) (G : Matrix (Fin p) (Fin m) ℝ)
    (H : Matrix (Fin p) (Fin l) ℝ) (τ : Fin n → ℝ) : Fin l → ℝ :=
  (barG G H * (leftPinv Jh)ᵀ) *ᵥ τ

/-- **The algebra of MLS eq. (6.33), p. 291, "we write the dynamics in terms of the velocities
`w`":** if `ẋ = H w`, `ẍ = H ẇ + Ḣ w`, `θ̇ = J_h⁺ Ḡᵀ w` and `θ̈ = J_h⁺ Ḡᵀ ẇ + Ẏ w`, then
`Hᵀ (M_o ẍ + C_o ẋ + N_o) + Ḡ J_h⁺ᵀ (M_f θ̈ + C_f θ̇ + N_f) = M̃ ẇ + C̃ w + Ñ`. -/
theorem reduced_dynamics_eq (Mo Co : Matrix (Fin p) (Fin p) ℝ) (No : Fin p → ℝ)
    (Mf Cf : Matrix (Fin n) (Fin n) ℝ) (Nf : Fin n → ℝ) (Jh : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin p) (Fin m) ℝ) (H Hd : Matrix (Fin p) (Fin l) ℝ) (Bd : Matrix (Fin n) (Fin l) ℝ)
    {w w' : Fin l → ℝ} {x' x'' : Fin p → ℝ} {θ' θ'' : Fin n → ℝ} (hx : x' = H *ᵥ w)
    (hxx : x'' = H *ᵥ w' + Hd *ᵥ w) (hv : θ' = (leftPinv Jh * (barG G H)ᵀ) *ᵥ w)
    (ha : θ'' = (leftPinv Jh * (barG G H)ᵀ) *ᵥ w' + Bd *ᵥ w) :
    Hᵀ *ᵥ (Mo *ᵥ x'' + Co *ᵥ x' + No) +
        (barG G H * (leftPinv Jh)ᵀ) *ᵥ (Mf *ᵥ θ'' + Cf *ᵥ θ' + Nf) =
      reducedMass Mo Mf Jh G H *ᵥ w' + reducedCoriolis Co Mo Cf Mf Jh G H Hd Bd *ᵥ w +
        reducedN No Nf Jh G H := by
  subst hx hxx hv ha
  simp only [reducedMass, reducedCoriolis, reducedN, Matrix.add_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_mulVec, Matrix.mul_add, Matrix.mul_assoc]
  abel

/-! ### The constraint `[J_h −Gᵀ]` with a rectangular `J_h` (MLS pp. 267, 289, 291)

The constraint matrix is the library's `graspPfaffian` (`Dynamics/RedundantDynamics`, MLS p. 289),
`A(q) = [J_h(q) −Gᵀ(q)]` with a rectangular `J_h`; `pfaffianAt_graspPfaffian_iff` there says that
`A q̇ = 0` is `J_h θ̇ = Gᵀ ẋ`. -/

variable {N : ℕ}

private theorem colsFst_graspPfaffian' (e : Fin p ⊕ Fin n ≃ Fin N)
    (Jh : (Fin N → ℝ) → Matrix (Fin m) (Fin n) ℝ) (G : (Fin N → ℝ) → Matrix (Fin p) (Fin m) ℝ)
    (q : Fin N → ℝ) : colsFst (graspPfaffian e Jh G q) e = -(G q)ᵀ := by
  ext i a
  simp [colsFst, graspPfaffian]

private theorem colsSnd_graspPfaffian' (e : Fin p ⊕ Fin n ≃ Fin N)
    (Jh : (Fin N → ℝ) → Matrix (Fin m) (Fin n) ℝ) (G : (Fin N → ℝ) → Matrix (Fin p) (Fin m) ℝ)
    (q : Fin N → ℝ) : colsSnd (graspPfaffian e Jh G q) e = Jh q := by
  ext i b
  simp [colsSnd, graspPfaffian]

private theorem dotProduct_reduced (y₁ : Fin p → ℝ) (y₂ : Fin n → ℝ) (H : Matrix (Fin p) (Fin l) ℝ)
    (X : Matrix (Fin n) (Fin l) ℝ) (δw : Fin l → ℝ) :
    y₁ ⬝ᵥ (H *ᵥ δw) + y₂ ⬝ᵥ (X *ᵥ δw) = (Hᵀ *ᵥ y₁ + Xᵀ *ᵥ y₂) ⬝ᵥ δw := by
  rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, add_dotProduct, Matrix.mulVec_transpose,
    Matrix.mulVec_transpose]

/-- **MLS printed p. 291: the virtual displacements of a nonmanipulable grasp are `δx = H δw`,
`δθ = J_h⁺ Ḡᵀ δw`, so a generalized force `y` does no virtual work for `[J_h −Gᵀ]` exactly when
`Hᵀ y_x + Ḡ J_h⁺ᵀ y_θ = 0`.** Hypotheses: `J_h` injective (full column rank, p. 290) and the columns
of `H` spanning `W` (p. 291). -/
theorem doesNoVirtualWork_graspPfaffian_iff_reduced (e : Fin p ⊕ Fin n ≃ Fin N)
    {Jh : (Fin N → ℝ) → Matrix (Fin m) (Fin n) ℝ} {G : (Fin N → ℝ) → Matrix (Fin p) (Fin m) ℝ}
    {q : Fin N → ℝ} {H : Matrix (Fin p) (Fin l) ℝ} (hJ : Function.Injective (Jh q).mulVec)
    (hH : SpansAllowable H (Jh q) (G q)) (y : Fin N → ℝ) :
    DoesNoVirtualWork (graspPfaffian e Jh G q) y ↔
      Hᵀ *ᵥ splitFst e y + (barG (G q) H * (leftPinv (Jh q))ᵀ) *ᵥ splitSnd e y = 0 := by
  set X := leftPinv (Jh q) * (barG (G q) H)ᵀ with hX
  have hXt : Xᵀ = barG (G q) H * (leftPinv (Jh q))ᵀ := by
    rw [hX, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [← hXt]
  have hmem : ∀ δw : Fin l → ℝ, ∃ θ0, Jh q *ᵥ θ0 = (G q)ᵀ *ᵥ (H *ᵥ δw) := by
    intro δw
    have h : H *ᵥ δw ∈ allowableVelocities (Jh q) (G q) := by
      rw [← hH]
      exact ⟨δw, rfl⟩
    exact (mem_allowableVelocities _ _ _).mp h
  constructor
  · intro hw
    set z := Hᵀ *ᵥ splitFst e y + Xᵀ *ᵥ splitSnd e y
    have hz : ∀ δw, z ⬝ᵥ δw = 0 := by
      intro δw
      obtain ⟨θ0, hθ0⟩ := hmem δw
      have hadm : graspPfaffian e Jh G q *ᵥ splitJoin e (H *ᵥ δw) (X *ᵥ δw) = 0 := by
        rw [mulVec_split _ e, colsFst_graspPfaffian', colsSnd_graspPfaffian', splitFst_splitJoin,
          splitSnd_splitJoin, hX, ← Matrix.mulVec_mulVec, barG_transpose, ← Matrix.mulVec_mulVec,
          mulVec_leftPinv_mulVec_of_eq hJ hθ0, Matrix.neg_mulVec, neg_add_cancel]
      have h := hw _ hadm
      rw [dotProduct_split e, splitFst_splitJoin, splitSnd_splitJoin, dotProduct_reduced] at h
      exact h
    exact dotProduct_self_eq_zero.mp (hz z)
  · intro hz δq hδ
    rw [mulVec_split _ e, colsFst_graspPfaffian', colsSnd_graspPfaffian', Matrix.neg_mulVec,
      neg_add_eq_sub, sub_eq_zero] at hδ
    have h1 : splitFst e δq ∈ allowableVelocities (Jh q) (G q) :=
      (mem_allowableVelocities _ _ _).mpr ⟨_, hδ⟩
    rw [← hH] at h1
    obtain ⟨δw, hδw⟩ := h1
    simp only [Matrix.mulVecLin_apply] at hδw
    have h2 : splitSnd e δq = X *ᵥ δw := by
      rw [eq_leftPinv_mulVec_of_eq hJ hδ, ← hδw, hX, barG_transpose, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [dotProduct_split e, h2, ← hδw, dotProduct_reduced, hz, zero_dotProduct]

/-- **MLS printed p. 291: the velocities and accelerations of a motion obeying (6.32).** Along a
motion with `J_h(s) θ'(s) = G(s)ᵀ x'(s)`, `x'(s) = H(s) w(s)` and `J_h(s)` injective for `s` near
`t`, with the entries of `H` and of `s ↦ J_h(s)⁺ Ḡ(s)ᵀ` having the derivatives `Hd` and `Bd` at `t`:
if `θ'`, `x'`, `w` have the derivatives `θ''`, `x''`, `w'` at `t`, then `x' = H w`,
`x'' = H w' + Hd w`, `θ' = J_h⁺ Ḡᵀ w` and `θ'' = J_h⁺ Ḡᵀ w' + Bd w` at `t`. -/
theorem velocity_acceleration_eq_reduced {J : ℝ → Matrix (Fin m) (Fin n) ℝ}
    {G : ℝ → Matrix (Fin p) (Fin m) ℝ} {H : ℝ → Matrix (Fin p) (Fin l) ℝ} {θ' : ℝ → Fin n → ℝ}
    {x' : ℝ → Fin p → ℝ} {w : ℝ → Fin l → ℝ} {θ'' : Fin n → ℝ} {x'' : Fin p → ℝ}
    {w' : Fin l → ℝ} {Hd : Matrix (Fin p) (Fin l) ℝ} {Bd : Matrix (Fin n) (Fin l) ℝ} {t : ℝ}
    (hc : ∀ᶠ s in 𝓝 t, J s *ᵥ θ' s = (G s)ᵀ *ᵥ x' s) (hx : ∀ᶠ s in 𝓝 t, x' s = H s *ᵥ w s)
    (hJ : ∀ᶠ s in 𝓝 t, Function.Injective (J s).mulVec)
    (hHd : ∀ i j, HasDerivAt (fun s => H s i j) (Hd i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => (leftPinv (J s) * (barG (G s) (H s))ᵀ) i j) (Bd i j) t)
    (hθ' : HasDerivAt θ' θ'' t) (hx' : HasDerivAt x' x'' t) (hw : HasDerivAt w w' t) :
    x' t = H t *ᵥ w t ∧ x'' = H t *ᵥ w' + Hd *ᵥ w t ∧
      θ' t = (leftPinv (J t) * (barG (G t) (H t))ᵀ) *ᵥ w t ∧
        θ'' = (leftPinv (J t) * (barG (G t) (H t))ᵀ) *ᵥ w' + Bd *ᵥ w t := by
  have hev : ∀ᶠ s in 𝓝 t, θ' s = (leftPinv (J s) * (barG (G s) (H s))ᵀ) *ᵥ w s := by
    filter_upwards [hc, hx, hJ] with s h1 h2 h3
    rw [eq_leftPinv_mulVec_of_eq h3 h1, h2, barG_transpose, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨hx.self_of_nhds, ?_, hev.self_of_nhds, ?_⟩
  · have h1 := (Control.hasDerivAt_matrix_mulVec_rect hHd hw).congr_of_eventuallyEq hx
    rw [hx'.unique h1, add_comm]
  · have h1 := (Control.hasDerivAt_matrix_mulVec_rect hB hw).congr_of_eventuallyEq hev
    rw [hθ'.unique h1, add_comm]

private theorem hasDerivAt_splitFst' (e : Fin p ⊕ Fin n ≃ Fin N) {q : ℝ → Fin N → ℝ}
    {q' : Fin N → ℝ} {s : ℝ} (h : HasDerivAt q q' s) :
    HasDerivAt (fun s => splitFst e (q s)) (splitFst e q') s :=
  hasDerivAt_pi.mpr fun a => hasDerivAt_pi.mp h (e (Sum.inl a))

private theorem hasDerivAt_splitSnd' (e : Fin p ⊕ Fin n ≃ Fin N) {q : ℝ → Fin N → ℝ}
    {q' : Fin N → ℝ} {s : ℝ} (h : HasDerivAt q q' s) :
    HasDerivAt (fun s => splitSnd e (q s)) (splitSnd e q') s :=
  hasDerivAt_pi.mpr fun b => hasDerivAt_pi.mp h (e (Sum.inr b))

/-- **MLS eq. (6.33), p. 291, derived from (6.32): the dynamics of a nonmanipulable grasp,**
`M̃ ẇ + C̃ w + Ñ = F`. For mechanical finger and object Lagrangians (6.19) with symmetric inertia
fields and Fréchet derivative data at `θ(t)`, `x(t)`, along a motion `q` with velocity `q'` near `t`
and acceleration `q''` at `t` on which the grasp constraint `[J_h −Gᵀ] q̇ = 0` and `ẋ = H w` hold
near `t` (the constraint (6.32)), with `J_h(q(s))` injective near `t`, the columns of `H(q(t))`
spanning `W` at `t`, and actual derivatives `w'` of `w`, `Hd` of `s ↦ H(q(s))` and `Bd` of
`s ↦ J_h⁺ Ḡᵀ` at `t`: the Lagrange–d'Alembert equations with the force `(τ, 0)` hold at `t` exactly
when `M̃ w' + C̃ w + Ñ = Ḡ J_h⁺ᵀ τ` with the derived parameters (`C_o`, `C_f` the Christoffel Coriolis
matrices, `N_o = ∂V_o/∂x`, `N_f = ∂V_f/∂θ`). Corrected printing: the object terms carry `H`. -/
theorem lagrangeDAlembertAt_graspPfaffian_iff_reduced (e : Fin p ⊕ Fin n ≃ Fin N)
    {Mo : (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ} {Mo' : Fin p → Fin p → ((Fin p → ℝ) →L[ℝ] ℝ)}
    {Vo : (Fin p → ℝ) → ℝ} {Vo' : (Fin p → ℝ) →L[ℝ] ℝ}
    {Mf : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {Mf' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)}
    {Vf : (Fin n → ℝ) → ℝ} {Vf' : (Fin n → ℝ) →L[ℝ] ℝ}
    {Jh : (Fin N → ℝ) → Matrix (Fin m) (Fin n) ℝ} {G : (Fin N → ℝ) → Matrix (Fin p) (Fin m) ℝ}
    {H : (Fin N → ℝ) → Matrix (Fin p) (Fin l) ℝ} {q q' : ℝ → Fin N → ℝ} {q'' : Fin N → ℝ}
    {w : ℝ → Fin l → ℝ} {w' : Fin l → ℝ} {Hd : Matrix (Fin p) (Fin l) ℝ}
    {Bd : Matrix (Fin n) (Fin l) ℝ} {t : ℝ}
    (hMo_symm : ∀ y, (Mo y).IsSymm) (hMf_symm : ∀ y, (Mf y).IsSymm)
    (hMo : ∀ i j, HasFDerivAt (fun y => Mo y i j) (Mo' i j) (splitFst e (q t)))
    (hVo : HasFDerivAt Vo Vo' (splitFst e (q t)))
    (hMf : ∀ i j, HasFDerivAt (fun y => Mf y i j) (Mf' i j) (splitSnd e (q t)))
    (hVf : HasFDerivAt Vf Vf' (splitSnd e (q t))) (hq : ∀ᶠ s in 𝓝 t, HasDerivAt q (q' s) s)
    (hq' : HasDerivAt q' q'' t)
    (hc : ∀ᶠ s in 𝓝 t, PfaffianAt (graspPfaffian e Jh G) (q s) (q' s))
    (hx : ∀ᶠ s in 𝓝 t, splitFst e (q' s) = H (q s) *ᵥ w s)
    (hJ : ∀ᶠ s in 𝓝 t, Function.Injective (Jh (q s)).mulVec)
    (hH : SpansAllowable (H (q t)) (Jh (q t)) (G (q t))) (hw : HasDerivAt w w' t)
    (hHd : ∀ i j, HasDerivAt (fun s => H (q s) i j) (Hd i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => (leftPinv (Jh (q s)) * (barG (G (q s)) (H (q s)))ᵀ) i j)
      (Bd i j) t)
    (τ : Fin n → ℝ) :
    LagrangeDAlembertAt (lagrangian e (Lagrangian.mechanical Mo Vo) (Lagrangian.mechanical Mf Vf))
        (graspPfaffian e Jh G) q (handForce e τ) t ↔
      reducedMass (Mo (splitFst e (q t))) (Mf (splitSnd e (q t))) (Jh (q t)) (G (q t)) (H (q t)) *ᵥ
            w' +
          reducedCoriolis
              (Christoffel.coriolisMatrix (Christoffel.partials Mo') (splitFst e (q' t)))
              (Mo (splitFst e (q t)))
              (Christoffel.coriolisMatrix (Christoffel.partials Mf') (splitSnd e (q' t)))
              (Mf (splitSnd e (q t))) (Jh (q t)) (G (q t)) (H (q t)) Hd Bd *ᵥ w t +
          reducedN (Lagrangian.gradient Vo') (Lagrangian.gradient Vf') (Jh (q t)) (G (q t))
            (H (q t)) =
        reducedForce (Jh (q t)) (G (q t)) (H (q t)) τ := by
  set Ro := Mo (splitFst e (q t)) *ᵥ splitFst e q'' +
    Christoffel.coriolisMatrix (Christoffel.partials Mo') (splitFst e (q' t)) *ᵥ
      splitFst e (q' t) + Lagrangian.gradient Vo'
  set Rf := Mf (splitSnd e (q t)) *ᵥ splitSnd e q'' +
    Christoffel.coriolisMatrix (Christoffel.partials Mf') (splitSnd e (q' t)) *ᵥ
      splitSnd e (q' t) + Lagrangian.gradient Vf'
  have hxq : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => splitFst e (q s)) (splitFst e (q' s)) s := by
    filter_upwards [hq] with s hs
    exact hasDerivAt_splitFst' e hs
  have hθq : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => splitSnd e (q s)) (splitSnd e (q' s)) s := by
    filter_upwards [hq] with s hs
    exact hasDerivAt_splitSnd' e hs
  have hRo := lagrangeEquationsAt_mechanical_inertial hMo_symm hMo hVo hxq
    (hasDerivAt_splitFst' e hq')
  have hRf := lagrangeEquationsAt_mechanical_inertial hMf_symm hMf hVf hθq
    (hasDerivAt_splitSnd' e hq')
  have hR : Lagrangian.LagrangeEquationsAt
      (lagrangian e (Lagrangian.mechanical Mo Vo) (Lagrangian.mechanical Mf Vf)) q
      (splitJoin e Ro Rf) t :=
    (lagrangeEquationsAt_lagrangian_iff e _ _ hq _).mpr
      ⟨by rwa [splitFst_splitJoin], by rwa [splitSnd_splitJoin]⟩
  have hc' : ∀ᶠ s in 𝓝 t, Jh (q s) *ᵥ splitSnd e (q' s) = (G (q s))ᵀ *ᵥ splitFst e (q' s) := by
    filter_upwards [hc] with s hs
    exact (pfaffianAt_graspPfaffian_iff e Jh G _ _).mp hs
  obtain ⟨hv1, hv2, hv3, hv4⟩ := velocity_acceleration_eq_reduced (J := fun s => Jh (q s))
    (G := fun s => G (q s)) (H := fun s => H (q s)) hc' hx hJ hHd hB
    (hasDerivAt_splitSnd' e hq') (hasDerivAt_splitFst' e hq') hw
  have key := reduced_dynamics_eq (Mo (splitFst e (q t)))
    (Christoffel.coriolisMatrix (Christoffel.partials Mo') (splitFst e (q' t)))
    (Lagrangian.gradient Vo') (Mf (splitSnd e (q t)))
    (Christoffel.coriolisMatrix (Christoffel.partials Mf') (splitSnd e (q' t)))
    (Lagrangian.gradient Vf') (Jh (q t)) (G (q t)) (H (q t)) Hd Bd hv1 hv2 hv3 hv4
  rw [lagrangeDAlembertAt_iff_of_lagrangeEquationsAt hR,
    doesNoVirtualWork_graspPfaffian_iff_reduced e hJ.self_of_nhds hH, handForce]
  have hsub1 : splitFst e (splitJoin e Ro Rf - splitJoin e 0 τ) = Ro := by
    funext a
    simp [splitFst, splitJoin]
  have hsub2 : splitSnd e (splitJoin e Ro Rf - splitJoin e 0 τ) = Rf - τ := by
    funext b
    simp [splitSnd, splitJoin]
  rw [hsub1, hsub2, Matrix.mulVec_sub, ← add_sub_assoc, key, reducedForce, sub_eq_zero]

/-! ### The printed form at `H = I` and the structure of `M̃` (MLS pp. 278–279, 291) -/

/-- **MLS eq. (6.33) at `H = I` with `J_h` invertible is (6.22) (pp. 278, 291):** the derived inertia
is `M_o + G J_h⁻ᵀ M_f J_h⁻¹ Gᵀ`, the printed display of p. 291 read with `l = p`. -/
theorem reducedMass_one {Mo : Matrix (Fin p) (Fin p) ℝ} {Mf Jh : Matrix (Fin n) (Fin n) ℝ}
    (hJ : IsUnit Jh.det) (G : Matrix (Fin p) (Fin n) ℝ) :
    reducedMass Mo Mf Jh G 1 = effectiveMass Mo Mf Jh G := by
  rw [reducedMass, effectiveMass, leftPinv_eq_inv hJ, barG, Matrix.transpose_one, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul]

/-- **MLS eq. (6.33) at `H = I` (so `Ḣ = 0`) with `J_h` invertible is (6.22) (pp. 278, 291):** the
derived Coriolis matrix is `C_o + G J_h⁻ᵀ (C_f J_h⁻¹ Gᵀ + M_f Ẏ)`. -/
theorem reducedCoriolis_one {Co Mo : Matrix (Fin p) (Fin p) ℝ} {Cf Mf Jh : Matrix (Fin n) (Fin n) ℝ}
    (hJ : IsUnit Jh.det) (G : Matrix (Fin p) (Fin n) ℝ) (Bd : Matrix (Fin n) (Fin p) ℝ) :
    reducedCoriolis Co Mo Cf Mf Jh G 1 0 Bd = effectiveCoriolis Co Cf Mf Jh G Bd := by
  rw [reducedCoriolis, effectiveCoriolis, leftPinv_eq_inv hJ, barG, Matrix.transpose_one,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul]
  simp only [Matrix.mul_assoc]

/-- **MLS eq. (6.33) at `H = I` with `J_h` invertible is (6.22) (pp. 278, 291):** `Ñ` and `F` are
`N_o + G J_h⁻ᵀ N_f` and `G J_h⁻ᵀ τ`. -/
theorem reducedN_one_and_reducedForce_one {Jh : Matrix (Fin n) (Fin n) ℝ} (hJ : IsUnit Jh.det)
    (G : Matrix (Fin p) (Fin n) ℝ) (No : Fin p → ℝ) (Nf τ : Fin n → ℝ) :
    reducedN No Nf Jh G 1 = effectiveN No Nf Jh G ∧
      reducedForce Jh G 1 τ = effectiveForce Jh G τ := by
  refine ⟨?_, ?_⟩
  · rw [reducedN, effectiveN, leftPinv_eq_inv hJ, barG, Matrix.transpose_one, Matrix.one_mulVec,
      Matrix.one_mul]
  · rw [reducedForce, effectiveForce, leftPinv_eq_inv hJ, barG, Matrix.transpose_one,
      Matrix.one_mul]

/-- **The inertia of (6.33) is a sum of congruences (MLS p. 291):**
`M̃ = Hᵀ M_o H + Xᵀ M_f X` with `X = J_h⁺ Ḡᵀ`. -/
theorem reducedMass_eq (Mo : Matrix (Fin p) (Fin p) ℝ) (Mf : Matrix (Fin n) (Fin n) ℝ)
    (Jh : Matrix (Fin m) (Fin n) ℝ) (G : Matrix (Fin p) (Fin m) ℝ) (H : Matrix (Fin p) (Fin l) ℝ) :
    reducedMass Mo Mf Jh G H =
      Hᵀ * Mo * H + (leftPinv Jh * (barG G H)ᵀ)ᵀ * Mf * (leftPinv Jh * (barG G H)ᵀ) := by
  rw [reducedMass, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

/-- **The inertia of (6.33) is symmetric (MLS p. 291 with Lemma 6.1(1), p. 279)** for symmetric
`M_o` and `M_f`. -/
theorem reducedMass_isSymm {Mo : Matrix (Fin p) (Fin p) ℝ} {Mf : Matrix (Fin n) (Fin n) ℝ}
    (hMo : Mo.IsSymm) (hMf : Mf.IsSymm) (Jh : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin p) (Fin m) ℝ) (H : Matrix (Fin p) (Fin l) ℝ) :
    (reducedMass Mo Mf Jh G H).IsSymm := by
  rw [reducedMass_eq]
  refine Matrix.IsSymm.add ?_ ?_
  · rw [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hMo.eq, Matrix.mul_assoc]
  · have hc : ∀ B : Matrix (Fin n) (Fin l) ℝ, (Bᵀ * Mf * B)ᵀ = Bᵀ * Mf * B := fun B => by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hMf.eq,
        Matrix.mul_assoc]
    exact hc _

/-- **The inertia of (6.33) is positive definite (MLS p. 291 with Lemma 6.1(1), p. 279)** for
`M_o` positive definite, `M_f` positive semidefinite and `H` injective (the `l` columns of `H` span
the `l`-dimensional `W`, p. 291). -/
theorem reducedMass_posDef {Mo : Matrix (Fin p) (Fin p) ℝ} {Mf : Matrix (Fin n) (Fin n) ℝ}
    (hMo : Mo.PosDef) (hMf : Mf.PosSemidef) (Jh : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin p) (Fin m) ℝ) {H : Matrix (Fin p) (Fin l) ℝ}
    (hH : Function.Injective H.mulVec) : (reducedMass Mo Mf Jh G H).PosDef := by
  rw [reducedMass_eq]
  have h1 := hMo.conjTranspose_mul_mul_same hH
  have h2 := hMf.conjTranspose_mul_mul_same (leftPinv Jh * (barG G H)ᵀ)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1 h2
  exact h1.add_posSemidef h2

/-- **The skew property of (6.33) at one instant (MLS p. 291 with Lemma 6.1(2), p. 279, and p. 300,
"These properties hold for all of the systems given in this chapter").** With `X = J_h⁺ Ḡᵀ`,
`Ẋ = Bd`, `Ḣ = Hd`, symmetric `M_o`, `M_f` and rates `Ṁ_o = Mod`, `Ṁ_f = Mfd` such that
`Ṁ_o − 2C_o` and `Ṁ_f − 2C_f` are skew, the rate
`Ḣᵀ M_o H + Hᵀ Ṁ_o H + Hᵀ M_o Ḣ + Ẋᵀ M_f X + Xᵀ Ṁ_f X + Xᵀ M_f Ẋ` of `M̃` minus `2C̃` is skew. -/
theorem skew_reducedMassRate_sub_two_reducedCoriolis {Mo Mod Co : Matrix (Fin p) (Fin p) ℝ}
    {Mf Mfd Cf : Matrix (Fin n) (Fin n) ℝ} (Jh : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin p) (Fin m) ℝ) (H Hd : Matrix (Fin p) (Fin l) ℝ) (Bd : Matrix (Fin n) (Fin l) ℝ)
    (hMo : Moᵀ = Mo) (hMf : Mfᵀ = Mf) (hso : (Mod - (2 : ℝ) • Co)ᵀ = -(Mod - (2 : ℝ) • Co))
    (hsf : (Mfd - (2 : ℝ) • Cf)ᵀ = -(Mfd - (2 : ℝ) • Cf)) :
    (Hdᵀ * Mo * H + Hᵀ * Mod * H + Hᵀ * Mo * Hd +
          (Bdᵀ * Mf * (leftPinv Jh * (barG G H)ᵀ) +
            (leftPinv Jh * (barG G H)ᵀ)ᵀ * Mfd * (leftPinv Jh * (barG G H)ᵀ) +
              (leftPinv Jh * (barG G H)ᵀ)ᵀ * Mf * Bd) -
        (2 : ℝ) • reducedCoriolis Co Mo Cf Mf Jh G H Hd Bd)ᵀ =
      -(Hdᵀ * Mo * H + Hᵀ * Mod * H + Hᵀ * Mo * Hd +
          (Bdᵀ * Mf * (leftPinv Jh * (barG G H)ᵀ) +
            (leftPinv Jh * (barG G H)ᵀ)ᵀ * Mfd * (leftPinv Jh * (barG G H)ᵀ) +
              (leftPinv Jh * (barG G H)ᵀ)ᵀ * Mf * Bd) -
        (2 : ℝ) • reducedCoriolis Co Mo Cf Mf Jh G H Hd Bd) := by
  set X := leftPinv Jh * (barG G H)ᵀ with hX
  have hXt : barG G H * (leftPinv Jh)ᵀ = Xᵀ := by
    rw [hX, Matrix.transpose_mul, Matrix.transpose_transpose]
  have e : Hdᵀ * Mo * H + Hᵀ * Mod * H + Hᵀ * Mo * Hd +
        (Bdᵀ * Mf * X + Xᵀ * Mfd * X + Xᵀ * Mf * Bd) -
      (2 : ℝ) • reducedCoriolis Co Mo Cf Mf Jh G H Hd Bd =
      (Hdᵀ * Mo * H + Hᵀ * Mod * H + Hᵀ * Mo * Hd - (2 : ℝ) • (Hᵀ * (Co * H + Mo * Hd))) +
        (Bdᵀ * Mf * X + Xᵀ * Mfd * X + Xᵀ * Mf * Bd - (2 : ℝ) • (Xᵀ * (Cf * X + Mf * Bd))) := by
    rw [reducedCoriolis, hXt, ← hX, Matrix.mul_assoc Xᵀ]
    module
  rw [e, Matrix.transpose_add, Control.skew_reduced hMo hso, Control.skew_reduced hMf hsf, neg_add]

end Composite
end RoboLean
