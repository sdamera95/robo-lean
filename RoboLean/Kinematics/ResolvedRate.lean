import RoboLean.Kinematics.RedundantManipulator
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Resolved-rate motion: integrating `θ̇ = (Jˢ)⁻¹ Vˢ` (MLS eq. (3.57))

MLS printed pp. 117–118: "If `J_st` is invertible, then we can write `θ̇(t) = (Jˢ_st(θ))⁻¹ Vˢ_st(t)`
(3.57). If `Vˢ_st(t)` is known, equation (3.57) is an ordinary differential equation for `θ`. To
move the end-effector between two configurations `g₁` and `g₂`, we pick any workspace path `g(t)`
with `g(0) = g₁` and `g(T) = g₂`, calculate the spatial velocity `V̂ˢ = ġ g⁻¹`, and integrate
equation (3.57) over the interval `[0, T]`."

The book states no hypotheses for the claim that the integration reaches `g₂`. The theorems
below add them: the workspace path has a derivative at every time of `[0, T]`; the joint motion
`θ` is a solution of (3.57) on `[0, T]` (existence of the solution on the whole interval is
assumed, not proved); along it the Jacobian is invertible; and the motion starts at a joint
vector reaching `g₁`. Under these hypotheses the end-effector follows the path, `g_st(θ(t)) = g(t)`
for all `t ∈ [0, T]`, in particular `g_st(θ(T)) = g₂`.

The proof compares the two motions point by point: a point `x` carried by either motion has
velocity `ωˢ × p + vˢ` with the same twist (MLS eq. (2.54), p. 54, and eq. (3.54), p. 116), so
the difference `d` of the two trajectories satisfies `ḋ = ωˢ × d`, its squared length is
constant, and it vanishes at `t = 0`.

Conventions: twists `(v, ω)`, the spatial velocity of `RigidTransform.spatialVelocity` (MLS
eq. (2.53), p. 53), six Jacobian rows `(v, ω)` numbered `0, …, 5` (`spatialJacobianRows`),
Lean column `i` is the book's column `i + 1`, real joint lift.
-/

noncomputable section

open Matrix Set

namespace RoboLean

namespace SerialChain

variable {n : ℕ}

/-- A rigid transform is determined by its action on points. -/
private theorem eq_of_forall_applyPoint {g h : RigidTransform}
    (H : ∀ x, g.applyPoint x = h.applyPoint x) : g = h := by
  have ht : g.translation = h.translation := by
    simpa [RigidTransform.applyPoint] using H 0
  have hr : ∀ x, g.rotation.act x = h.rotation.act x := by
    intro x
    have := H x
    simp only [RigidTransform.applyPoint, ht] at this
    exact add_right_cancel this
  apply RigidTransform.ext _ ht
  apply Subtype.ext
  ext i j
  have := congrArg (fun v : Vec3 => v i) (hr (EuclideanSpace.single j 1))
  simpa [Rotation.act_apply, Matrix.mulVec_single] using this

private theorem rows_sum_eq_iff (c : SerialChain n) (θ x : Fin n → ℝ) (V : Twist) :
    ∑ i, x i • c.spatialJacobian θ i = V ↔
      c.spatialJacobianRows θ *ᵥ x = V.coordinates ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm := by
  have hrows : c.spatialJacobianRows θ *ᵥ x =
      (∑ i, x i • c.spatialJacobian θ i).coordinates ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm := by
    change (c.spatialJacobianMatrix θ *ᵥ x) ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm = _
    rw [spatialJacobianMatrix_mulVec]
  rw [hrows]
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Twist.coordinatesEquiv.injective
    funext r
    have := congrFun h ((finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6) r)
    simp only [Function.comp_apply, Equiv.symm_apply_apply] at this
    exact this

/-- **MLS eq. (3.57), p. 117, read pointwise (the converse direction).** A joint motion whose rates
satisfy `Jˢ(θ) θ̇ = Vˢ` at `t` (for example `θ̇ = (Jˢ)⁻¹ Vˢ` with `Jˢ` invertible) gives the
end-effector the spatial velocity `Vˢ` at `t`, for every chain and every derivative `D` of the
homogeneous forward kinematics. -/
theorem spatialVelocity_fk_eq_of_rates (c : SerialChain n) {θ : ℝ → Fin n → ℝ}
    {θ' : Fin n → ℝ} {t : ℝ} (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) {V : Twist}
    (hrate : ∑ i, θ' i • c.spatialJacobian (θ t) i = V) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (c.fk (θ s)).toHomogeneous) D t) :
    RigidTransform.spatialVelocity (fun s => c.fk (θ s)) D t hD = V := by
  rw [c.spatialVelocity_fk hθ hD, hrate]

/-- **MLS pp. 117–118: the end-effector follows the workspace path.** Let `g` be a workspace path
with a derivative `D t` of its homogeneous matrix at every `t ∈ [0, T]`, and `θ` a joint motion
with rates `θ̇(t)` on `[0, T]` that produce the path's spatial velocity,
`Jˢ(θ(t)) θ̇(t) = Vˢ(t)` with `V̂ˢ = ġ g⁻¹`, starting at `g_st(θ(0)) = g(0)`. Then
`g_st(θ(t)) = g(t)` for every `t ∈ [0, T]`. -/
theorem fk_eq_of_spatialVelocity (c : SerialChain n) {g : ℝ → RigidTransform}
    {D : ℝ → HomogeneousMatrix} {θ θ' : ℝ → Fin n → ℝ} {T : ℝ}
    (hg : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => (g s).toHomogeneous) (D t) t)
    (hθ : ∀ t ∈ Icc 0 T, ∀ i, HasDerivAt (fun s => θ s i) (θ' t i) t)
    (hrate : ∀ t (ht : t ∈ Icc 0 T),
      ∑ i, θ' t i • c.spatialJacobian (θ t) i = RigidTransform.spatialVelocity g (D t) t (hg t ht))
    (h0 : c.fk (θ 0) = g 0) : ∀ t ∈ Icc 0 T, c.fk (θ t) = g t := by
  intro t₁ ht₁
  apply (eq_of_forall_applyPoint fun x => ?_)
  set d : ℝ → Vec3 := fun s => (c.fk (θ s)).applyPoint x - (g s).applyPoint x
  have hd : ∀ s (hs : s ∈ Icc 0 T), HasDerivAt d (Vec3.cross
      (RigidTransform.spatialVelocity g (D s) s (hg s hs)).angular (d s)) s := by
    intro s hs
    have hD' := c.hasDerivAt_fk_toHomogeneous (hθ s hs)
    have hb := RigidTransform.hasDerivAt_applyPoint_spatial hD' x
    have ha := RigidTransform.hasDerivAt_applyPoint_spatial (hg s hs) x
    rw [c.spatialVelocity_fk_eq_of_rates (hθ s hs) (hrate s hs) hD'] at hb
    convert hb.sub ha using 1
    simp only [d, sub_eq_add_neg, Vec3.cross_add, Vec3.cross_neg]
    abel
  have hf : ∀ s ∈ Icc 0 T, HasDerivAt (fun s => inner ℝ (d s) (d s)) 0 s := by
    intro s hs
    convert HasDerivAt.inner ℝ (hd s hs) (hd s hs) using 1
    have h1 : inner ℝ (d s) (Vec3.cross
        (RigidTransform.spatialVelocity g (D s) s (hg s hs)).angular (d s)) = 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, Vec3.cross_coordinates, star_trivial,
        dotProduct_comm]
      exact dot_cross_self _ _
    rw [h1, real_inner_comm, h1]
    simp
  have hconst := constant_of_has_deriv_right_zero (f := fun s => inner ℝ (d s) (d s))
    (fun s hs => (hf s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hf s (Ico_subset_Icc_self hs)).hasDerivWithinAt) t₁ ht₁
  have hd0 : d 0 = 0 := by simp [d, h0]
  rw [hd0, inner_zero_left, real_inner_self_eq_norm_sq] at hconst
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hconst
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- **MLS eq. (3.57), pp. 117–118, with the hypotheses the book omits: integrating the
resolved-rate equation moves the end-effector from `g₁` to `g₂`.** For a six-joint chain, a
workspace path `g` from `g(0) = g₁` to `g(T) = g₂` with derivatives on `[0, T]`, and a joint motion
`θ` that solves `θ̇(t) = (Jˢ(θ(t)))⁻¹ Vˢ(t)` on `[0, T]` (six Jacobian rows `(v, ω)` numbered
`0, …, 5`, `V̂ˢ = ġ g⁻¹`), with `Jˢ(θ(t))` invertible at every `t ∈ [0, T]` and `g_st(θ(0)) = g₁`:
the end-effector follows the path, `g_st(θ(t)) = g(t)` on `[0, T]`, and `g_st(θ(T)) = g₂`. -/
theorem fk_eq_of_resolvedRate (c : SerialChain 6) {g : ℝ → RigidTransform}
    {D : ℝ → HomogeneousMatrix} {θ θ' : ℝ → Fin 6 → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hg : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => (g s).toHomogeneous) (D t) t)
    (hθ : ∀ t ∈ Icc 0 T, ∀ i, HasDerivAt (fun s => θ s i) (θ' t i) t)
    (hinv : ∀ t ∈ Icc 0 T, IsUnit (c.spatialJacobianRows (θ t)).det)
    (hode : ∀ t (ht : t ∈ Icc 0 T), θ' t = (c.spatialJacobianRows (θ t))⁻¹ *ᵥ
      ((RigidTransform.spatialVelocity g (D t) t (hg t ht)).coordinates ∘
        (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm))
    (h0 : c.fk (θ 0) = g 0) :
    (∀ t ∈ Icc 0 T, c.fk (θ t) = g t) ∧ c.fk (θ T) = g T := by
  have hrate : ∀ t (ht : t ∈ Icc 0 T), ∑ i, θ' t i • c.spatialJacobian (θ t) i =
      RigidTransform.spatialVelocity g (D t) t (hg t ht) := by
    intro t ht
    rw [c.rows_sum_eq_iff, hode t ht, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (hinv t ht), Matrix.one_mulVec]
  have h := c.fk_eq_of_spatialVelocity hg hθ hrate h0
  exact ⟨h, h T ⟨hT, le_rfl⟩⟩

end SerialChain

end RoboLean
