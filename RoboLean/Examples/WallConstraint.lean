import RoboLean.Examples.SlotConstraint

/-!
# A planar two-link manipulator pushing against a wall (MLS Chapter 6, Exercise 7, p. 315)

The end effector of the planar two-link arm stays on the wall `x = c` (figure of p. 315). The
wall is the slot of MLS §6.3 (p. 203) with `α = π/2` and `l = c`, the case the book names on
p. 203 ("easily adapted to a robot pushing against a wall"). Here:

* part (a), the kinematic constraint: `h(θ) = l₁ cos θ₁ + l₂ cos(θ₁ + θ₂) − c = 0` in joint
  coordinates (`wallJointConstraint_eq`), its gradient (`jac_wallJointConstraint`) and the
  velocity constraint `∇h(θ) · θ̇ = 0` along every motion on the wall
  (`wallJointConstraint_velocity`);
* parts (c)–(d) in workspace coordinates `w = (x, y)`: the constraint `x − c = 0` with the
  parameterization `y ↦ (c, y)`; for every robot `(M, C, N)` in workspace coordinates with `M`
  positive definite, the hybrid law (4.63) with commanded normal force `f_d` gives exponential
  (hence asymptotic) tracking of trajectories in `y`, and the constraint multiplier, the internal
  force of the wall, equals `f_d`, positive when `f_d > 0`, so the arm pushes and never pulls
  (`wall_tracking`).

**Differences from the exercise.** Part (b), the joint-space dynamics with point masses at the
middle of the links, is not formalized. Part (d) asks for "a PD controller"; the law here is the
hybrid computed torque law (4.63), PD error feedback with model compensation, which gives
exponential tracking. Unilateral contact is not modeled: the multiplier is computed, its sign is
the content of "pushing".
-/

noncomputable section

open Matrix Set

namespace RoboLean.Examples

open MapJacobian Control

/-- The wall `x = c` in workspace coordinates, `h(w) = x − c` (MLS Exercise 7(a), p. 315). -/
def wallConstraint (c : ℝ) (w : Fin 2 → ℝ) : Fin 1 → ℝ :=
  ![w 0 - c]

/-- The position along the wall, `y ↦ (c, y)` (MLS Exercise 7, p. 315). -/
def wallPath (c : ℝ) (y : Fin 1 → ℝ) : Fin 2 → ℝ :=
  ![c, y 0]

/-- The wall is the slot of MLS p. 203 with `α = π/2` and `l = c`: constraint. -/
theorem wallConstraint_eq_slotConstraint (c : ℝ) :
    wallConstraint c = slotConstraint c (Real.pi / 2) := by
  funext w i; fin_cases i
  simp [wallConstraint, slotConstraint]

/-- The wall is the slot of MLS p. 203 with `α = π/2` and `l = c`: parameterization. -/
theorem wallPath_eq_slotPath (c : ℝ) : wallPath c = slotPath c (Real.pi / 2) := by
  funext y i; fin_cases i <;> simp [wallPath, slotPath]

/-- The wall constraint in joint coordinates of the planar two-link arm (MLS Exercise 7(a),
p. 315): `h(θ) = l₁ cos θ₁ + l₂ cos(θ₁ + θ₂) − c`. -/
theorem wallJointConstraint_eq (l₁ l₂ c : ℝ) (θ : Fin 2 → ℝ) :
    wallConstraint c (planarArmXY l₁ l₂ θ) =
      ![l₁ * Real.cos (θ 0) + l₂ * Real.cos (θ 0 + θ 1) - c] := by
  funext i; fin_cases i
  simp [wallConstraint, planarArmXY]

/-- The gradient of the joint-space wall constraint (MLS Exercise 7(a), p. 315):
`∇h(θ) = (−l₁ sin θ₁ − l₂ sin(θ₁ + θ₂), −l₂ sin(θ₁ + θ₂))`. -/
theorem jac_wallJointConstraint (l₁ l₂ c : ℝ) (θ : Fin 2 → ℝ) :
    jac (fun q => wallConstraint c (planarArmXY l₁ l₂ q)) θ =
      !![-(l₁ * Real.sin (θ 0)) - l₂ * Real.sin (θ 0 + θ 1), -(l₂ * Real.sin (θ 0 + θ 1))] := by
  have e : (fun q => wallConstraint c (planarArmXY l₁ l₂ q)) =
      slotJointConstraint l₁ l₂ c (Real.pi / 2) := by
    funext q; simp only [slotJointConstraint, wallConstraint_eq_slotConstraint]
  rw [e, jac_slotJointConstraint]
  ext i j; fin_cases i; fin_cases j <;> simp [Real.cos_sub_pi_div_two]

/-- **The kinematic constraint of MLS Exercise 7(a), p. 315, in velocity form:** along every joint
motion `θ` that keeps the end effector on the wall and has velocity `θ'` at `t`,
`(−l₁ sin θ₁ − l₂ sin(θ₁ + θ₂)) θ̇₁ − l₂ sin(θ₁ + θ₂) θ̇₂ = 0`. -/
theorem wallJointConstraint_velocity (l₁ l₂ c : ℝ) {θ : ℝ → Fin 2 → ℝ} {θ' : Fin 2 → ℝ} {t : ℝ}
    (hθ : HasDerivAt θ θ' t) (hon : ∀ s, wallConstraint c (planarArmXY l₁ l₂ (θ s)) = 0) :
    (-(l₁ * Real.sin (θ t 0)) - l₂ * Real.sin (θ t 0 + θ t 1)) * θ' 0 -
      l₂ * Real.sin (θ t 0 + θ t 1) * θ' 1 = 0 := by
  have h0 : HasDerivAt (fun s => θ s 0) (θ' 0) t := hasDerivAt_pi.mp hθ 0
  have h1 : HasDerivAt (fun s => θ s 1) (θ' 1) t := hasDerivAt_pi.mp hθ 1
  have hd := ((h0.cos.const_mul l₁).add ((h0.add h1).cos.const_mul l₂)).sub_const c
  have hz : (fun s => l₁ * Real.cos (θ s 0) + l₂ * Real.cos (θ s 0 + θ s 1) - c) =
      fun _ => 0 := by
    funext s
    have := congrFun (hon s) 0
    simpa [wallConstraint, planarArmXY] using this
  have hd' : HasDerivAt (fun s => l₁ * Real.cos (θ s 0) + l₂ * Real.cos (θ s 0 + θ s 1) - c)
      (l₁ * (-Real.sin (θ t 0) * θ' 0) + l₂ * (-Real.sin (θ t 0 + θ t 1) * (θ' 0 + θ' 1))) t :=
    hd
  rw [hz] at hd'
  have := hd'.unique (hasDerivAt_const t (0 : ℝ))
  linear_combination this

/-- **MLS Exercise 7(c)–(d), p. 315, in workspace coordinates:** for every robot `(M, C, N)` in
workspace coordinates with `M` positive definite, positive gains and a commanded normal force
`f_d`, the hybrid law (4.63) for the wall gives exponential tracking of trajectories in `y`, and
the constraint multiplier (the internal force of the wall) equals `f_d`, positive for `f_d > 0`. -/
theorem wall_tracking (R : RobotSystem 2) (hM : ∀ q, (R.M q).PosDef) (c : ℝ)
    {Kp Kv : Matrix (Fin 1) (Fin 1) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) {fd : ℝ}
    (hfd : 0 < fd) :
    ∃ m₀ > 0, ∃ a > 0, ∀ {yd yd' yd'' : ℝ → Fin 1 → ℝ}, (∀ t, HasDerivAt yd (yd' t) t) →
      (∀ t, HasDerivAt yd' (yd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ (y y' y'' : ℝ → Fin 1 → ℝ)
      (μ : ℝ → Fin 1 → ℝ),
      ContinuousOn (fun t => (y t, y' t)) (Ici t₀) → (∀ t, t₀ < t → HasDerivAt y (y' t) t) →
      (∀ t, t₀ < t → HasDerivAt y' (y'' t) t) →
      (∀ t, t₀ < t → R.ConstrainedEquationsAt (wallConstraint c) (wallPath c (y t))
        (jac (wallPath c) (y t) *ᵥ y' t)
        (jac (wallPath c) (y t) *ᵥ y'' t + jacDot (wallPath c) (y t) (y' t) *ᵥ y' t)
        (R.hybridTorque (wallConstraint c) (wallPath c) Kp Kv (yd t) (yd' t) (yd'' t) (y t)
          (y' t) ![fd]) (μ t)) →
      (∀ t, t₀ ≤ t → ‖(y t - yd t, y' t - yd' t)‖ ≤
        m₀ * Real.exp (-a * (t - t₀)) * ‖(y t₀ - yd t₀, y' t₀ - yd' t₀)‖) ∧
      ∀ t, t₀ < t → μ t 0 = fd ∧ 0 < μ t 0 := by
  rw [wallConstraint_eq_slotConstraint, wallPath_eq_slotPath]
  obtain ⟨m₀, hm, a, ha, hT⟩ := slot_tracking R hM c (Real.pi / 2) hKp hKv
  refine ⟨m₀, hm, a, ha, fun {yd yd' yd''} hd hd' t₀ ht₀ y y' y'' μ hc hy hy' hE => ?_⟩
  obtain ⟨htrack, hμ⟩ := hT hd hd' t₀ ht₀ y y' y'' (fun _ => ![fd]) μ hc hy hy' hE
  refine ⟨htrack, fun t ht => ?_⟩
  have h := congrFun (hμ t ht) 0
  simp only [Matrix.cons_val_zero] at h
  exact ⟨h, h ▸ hfd⟩

end RoboLean.Examples
