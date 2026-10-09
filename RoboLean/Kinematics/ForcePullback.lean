import RoboLean.Kinematics.Jacobian
import RoboLean.Geometry.Wrench

/-!
# Force pullback: joint torques from an end-effector wrench

MLS Chapter 3, §4.2, printed p. 121, eqs. (3.59)–(3.60). The body form (3.59) is
`τ = (Jᵇ_st)ᵀ F_t` for a body wrench `F_t` applied at the tool-frame origin and written in
tool coordinates; the spatial form (3.60) is `τ = (Jˢ_st)ᵀ F_s` for a spatial wrench `F_s`.

Conventions. A Jacobian is the function `Fin n → Twist` of its columns, as in
`RoboLean.Kinematics.Jacobian`; Lean column `i` is the book's column `i + 1`. Wrench order
is `(f, τ)` (force, then moment) and twist order is `(v, ω)` (linear, then angular). The
joint torque of joint `i` is the pairing `Wrench.pair` of the wrench with Jacobian column
`i`, with wrench and Jacobian in matched frames: a spatial wrench with the spatial
Jacobian, a body wrench at the tool origin in tool coordinates with the body Jacobian. The
`6 × n` matrix forms `spatialJacobianMatrix` and `bodyJacobianMatrix` recover the book's
transpose formulas.

What is and is not formalized. The book derives (3.59) from the premise that, without
friction, the work done by the joints equals the work done by the end-effector wrench over
every time interval; equal integrals over every interval give equal integrands, and then
`θ̇ᵀ τ = θ̇ᵀ (Jᵇ)ᵀ F_t` gives (3.59) "since θ̇ is free". This file formalizes only the
instantaneous algebraic identity (the joint-side power equals the pairing of the wrench
with the end-effector velocity) and the uniqueness step "since θ̇ is free". It does not
formalize the frictionless physical premise, the time integral, or any physical claim
about a robot.

Spatial and body wrenches correspond by `Wrench.transform (c.fk θ)`: in the library's
direction convention a body wrench `F_b` is carried to the spatial wrench
`Wrench.transform (c.fk θ) F_b`, the inverse of MLS eq. (2.67), p. 63, `F_b = Ad_gᵀ F_s`.
-/

noncomputable section

open scoped Matrix

namespace RoboLean

namespace Wrench

/-- The twist–wrench pairing of MLS printed p. 61 (`f · v + τ · ω`) is the dot product of
the six coordinates, wrench order `(f, τ)` against twist order `(v, ω)`; this is the
coordinate form `Vᵀ F` used on p. 121. -/
theorem pair_eq_coordinates_dotProduct (F : Wrench) (ξ : Twist) :
    pair F ξ = F.coordinates ⬝ᵥ ξ.coordinates := by
  simp only [pair, coordinates, Twist.coordinates, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The pairing of MLS printed p. 61 is linear in the twist over a finite combination of
columns: pairing a wrench with `∑ i, θ̇ᵢ Jᵢ` gives `∑ i, (F · Jᵢ) θ̇ᵢ`. Wrench order
`(f, τ)`, twist order `(v, ω)`. -/
theorem pair_sum_smul {n : ℕ} (F : Wrench) (J : Fin n → Twist) (θ' : Fin n → ℝ) :
    pair F (∑ i, θ' i • J i) = ∑ i, pair F (J i) * θ' i := by
  calc pair F (∑ i, θ' i • J i) = pairing F (∑ i, θ' i • J i) := rfl
    _ = ∑ i, pairing F (θ' i • J i) := map_sum (pairing F) _ Finset.univ
    _ = ∑ i, pair F (J i) * θ' i :=
      Finset.sum_congr rfl fun i _ => by rw [pairing_apply, pair_smul_right, mul_comm]

end Wrench

namespace SerialChain

variable {n : ℕ}

/-- The joint torques equivalent to a spatial wrench `F_s` applied at the end-effector,
MLS printed p. 121, eq. (3.60), `τ = (Jˢ_st)ᵀ F_s`: torque `i` is the pairing of `F_s` with
spatial Jacobian column `i` (Lean column `i` = book column `i + 1`). Wrench order `(f, τ)`,
twist order `(v, ω)`; the wrench must be a spatial wrench, matched with the spatial
Jacobian. -/
def spatialWrenchTorques (c : SerialChain n) (θ : Fin n → ℝ) (F : Wrench) : Fin n → ℝ :=
  fun i => Wrench.pair F (c.spatialJacobian θ i)

/-- The joint torques equivalent to a body wrench `F_t` applied at the tool-frame origin
in tool coordinates, MLS printed p. 121, eq. (3.59), `τ = (Jᵇ_st)ᵀ F_t`: torque `i` is the
pairing of `F_t` with body Jacobian column `i` (Lean column `i` = book column `i + 1`).
Wrench order `(f, τ)`, twist order `(v, ω)`. -/
def bodyWrenchTorques (c : SerialChain n) (θ : Fin n → ℝ) (F : Wrench) : Fin n → ℝ :=
  fun i => Wrench.pair F (c.bodyJacobian θ i)

/-- The body Jacobian as a real `6 × n` matrix, MLS printed p. 117: the matrix form of
eq. (3.55), mirroring `spatialJacobianMatrix`; rows `Sum.inl` are `v`, `Sum.inr` are `ω`
(twist order `(v, ω)`), and column `i` holds `Twist.coordinates` of body column `i`
(Lean column `i` = book column `i + 1`). -/
def bodyJacobianMatrix (c : SerialChain n) (θ : Fin n → ℝ) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin n) ℝ :=
  Matrix.of fun r i => (c.bodyJacobian θ i).coordinates r

/-- Joint-side power equals the pairing of a spatial wrench with `Jˢ(θ) θ̇`, MLS printed
p. 121, the spatial analogue of `θ̇ᵀ τ = θ̇ᵀ (Jᵀ) F` behind eq. (3.60):
`∑ i, τᵢ θ̇ᵢ = F_s · (∑ i, θ̇ᵢ ξᵢ')` for `τ = spatialWrenchTorques`. Wrench `(f, τ)` and
twist `(v, ω)` in the spatial frame; Lean column `i` = book column `i + 1`. This is the
algebraic virtual-work identity (instantaneous power), not the frictionless
physical-work premise of p. 121 or a physical claim. -/
theorem sum_spatialWrenchTorques_mul (c : SerialChain n) (θ θ' : Fin n → ℝ) (F : Wrench) :
    ∑ i, c.spatialWrenchTorques θ F i * θ' i =
      Wrench.pair F (∑ i, θ' i • c.spatialJacobian θ i) :=
  (Wrench.pair_sum_smul F _ θ').symm

/-- Joint-side power equals the pairing of a body wrench with `Jᵇ(θ) θ̇`, MLS printed
p. 121, `θ̇ᵀ τ = θ̇ᵀ (Jᵇ_st)ᵀ F_t` before eq. (3.59): `∑ i, τᵢ θ̇ᵢ = F_t · (∑ i, θ̇ᵢ ξᵢ†)`
for `τ = bodyWrenchTorques`. Body wrench at the tool origin in tool coordinates, wrench
`(f, τ)`, twist `(v, ω)`; Lean column `i` = book column `i + 1`. This is the algebraic
virtual-work identity (instantaneous power), not the frictionless physical-work premise
of p. 121 or a physical claim. -/
theorem sum_bodyWrenchTorques_mul (c : SerialChain n) (θ θ' : Fin n → ℝ) (F : Wrench) :
    ∑ i, c.bodyWrenchTorques θ F i * θ' i =
      Wrench.pair F (∑ i, θ' i • c.bodyJacobian θ i) :=
  (Wrench.pair_sum_smul F _ θ').symm

/-- **MLS printed p. 121, eq. (3.60), uniqueness.** A joint-torque vector `τ` equals the
spatial pullback `(Jˢ_st)ᵀ F_s` if and only if its power `∑ i, τᵢ θ̇ᵢ` equals
`F_s · (Jˢ θ̇)` for every joint rate `θ̇`. This formalizes the step "since θ̇ is free" of
p. 121, in the spatial form. Spatial wrench `(f, τ)` with the spatial Jacobian, twist
`(v, ω)`, Lean column `i` = book column `i + 1`. It is the algebraic virtual-work identity
(instantaneous power), not the frictionless physical-work premise or a physical claim. -/
theorem eq_spatialWrenchTorques_iff (c : SerialChain n) (θ : Fin n → ℝ) (F : Wrench)
    (τ : Fin n → ℝ) :
    τ = c.spatialWrenchTorques θ F ↔
      ∀ θ' : Fin n → ℝ, ∑ i, τ i * θ' i = Wrench.pair F (∑ i, θ' i • c.spatialJacobian θ i) := by
  constructor
  · rintro rfl θ'
    exact c.sum_spatialWrenchTorques_mul θ θ' F
  · intro h
    funext j
    have hj := h (Pi.single j 1)
    rw [← c.sum_spatialWrenchTorques_mul θ (Pi.single j 1) F] at hj
    simpa [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq'] using hj

/-- **MLS printed p. 121, eq. (3.59), uniqueness.** A joint-torque vector `τ` equals the
body pullback `(Jᵇ_st)ᵀ F_t` if and only if its power `∑ i, τᵢ θ̇ᵢ` equals `F_t · (Jᵇ θ̇)`
for every joint rate `θ̇`. This formalizes the step "since θ̇ is free" of p. 121. Body
wrench at the tool origin in tool coordinates, wrench `(f, τ)`, twist `(v, ω)`, Lean
column `i` = book column `i + 1`. It is the algebraic virtual-work identity (instantaneous
power), not the frictionless physical-work premise or a physical claim. -/
theorem eq_bodyWrenchTorques_iff (c : SerialChain n) (θ : Fin n → ℝ) (F : Wrench)
    (τ : Fin n → ℝ) :
    τ = c.bodyWrenchTorques θ F ↔
      ∀ θ' : Fin n → ℝ, ∑ i, τ i * θ' i = Wrench.pair F (∑ i, θ' i • c.bodyJacobian θ i) := by
  constructor
  · rintro rfl θ'
    exact c.sum_bodyWrenchTorques_mul θ θ' F
  · intro h
    funext j
    have hj := h (Pi.single j 1)
    rw [← c.sum_bodyWrenchTorques_mul θ (Pi.single j 1) F] at hj
    simpa [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq'] using hj

/-- **MLS printed p. 121, eq. (3.60), along a trajectory.** For a joint trajectory with
actual derivatives `θ̇ᵢ`, the joint-side power `∑ i, τᵢ θ̇ᵢ` of the spatial pullback
`τ = (Jˢ_st)ᵀ F_s` equals the pairing of `F_s` with the actual spatial velocity of the
forward-kinematics curve. The derivative `D` exists by
`SerialChain.hasDerivAt_fk_toHomogeneous`, so the hypothesis `hD` is satisfiable. Spatial
wrench `(f, τ)`, twist `(v, ω)`, Lean column `i` = book column `i + 1`. This is the
algebraic virtual-work identity (instantaneous power), not the frictionless physical-work
premise, the time integral of p. 121, or a physical claim. -/
theorem sum_spatialWrenchTorques_mul_eq_pair_spatialVelocity (c : SerialChain n)
    {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ} {t : ℝ}
    (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (c.fk (θ s)).toHomogeneous) D t) (F : Wrench) :
    ∑ i, c.spatialWrenchTorques (θ t) F i * θ' i =
      Wrench.pair F (RigidTransform.spatialVelocity (fun s => c.fk (θ s)) D t hD) := by
  rw [c.spatialVelocity_fk hθ hD]
  exact c.sum_spatialWrenchTorques_mul (θ t) θ' F

/-- **MLS printed p. 121, eq. (3.59), along a trajectory.** For a joint trajectory with
actual derivatives `θ̇ᵢ`, the joint-side power `∑ i, τᵢ θ̇ᵢ` of the body pullback
`τ = (Jᵇ_st)ᵀ F_t` equals `Vᵇ_st · F_t`, the pairing of `F_t` with the actual body velocity
of the forward-kinematics curve (the integrand of `W` on p. 121). The derivative `D` exists
by `SerialChain.hasDerivAt_fk_toHomogeneous`, so the hypothesis `hD` is satisfiable. Body
wrench at the tool origin in tool coordinates, wrench `(f, τ)`, twist `(v, ω)`, Lean
column `i` = book column `i + 1`. This is the algebraic virtual-work identity
(instantaneous power), not the frictionless physical-work premise, the time integral of
p. 121, or a physical claim. -/
theorem sum_bodyWrenchTorques_mul_eq_pair_bodyVelocity (c : SerialChain n)
    {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ} {t : ℝ}
    (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (c.fk (θ s)).toHomogeneous) D t) (F : Wrench) :
    ∑ i, c.bodyWrenchTorques (θ t) F i * θ' i =
      Wrench.pair F (RigidTransform.bodyVelocity (fun s => c.fk (θ s)) D t hD) := by
  rw [c.bodyVelocity_fk hθ hD]
  exact c.sum_bodyWrenchTorques_mul (θ t) θ' F

/-- **MLS printed p. 121, eq. (3.60), matrix form.** The transpose of the `6 × n` spatial
Jacobian matrix applied to the six wrench coordinates is the spatial pullback,
`(Jˢ_st)ᵀ F_s = spatialWrenchTorques`. Spatial wrench coordinates `(f, τ)` against twist
rows `(v, ω)`; Lean column `i` = book column `i + 1`. -/
theorem spatialJacobianMatrix_transpose_mulVec (c : SerialChain n) (θ : Fin n → ℝ)
    (F : Wrench) :
    (c.spatialJacobianMatrix θ)ᵀ *ᵥ F.coordinates = c.spatialWrenchTorques θ F := by
  funext i
  change (c.spatialJacobian θ i).coordinates ⬝ᵥ F.coordinates = _
  rw [dotProduct_comm]
  exact (Wrench.pair_eq_coordinates_dotProduct F (c.spatialJacobian θ i)).symm

/-- **MLS printed p. 121, eq. (3.59), matrix form.** The transpose of the `6 × n` body
Jacobian matrix applied to the six coordinates of a body wrench (at the tool origin, in
tool coordinates) is the body pullback, `(Jᵇ_st)ᵀ F_t = bodyWrenchTorques`. Wrench
coordinates `(f, τ)` against twist rows `(v, ω)`; Lean column `i` = book column `i + 1`. -/
theorem bodyJacobianMatrix_transpose_mulVec (c : SerialChain n) (θ : Fin n → ℝ)
    (F : Wrench) :
    (c.bodyJacobianMatrix θ)ᵀ *ᵥ F.coordinates = c.bodyWrenchTorques θ F := by
  funext i
  change (c.bodyJacobian θ i).coordinates ⬝ᵥ F.coordinates = _
  rw [dotProduct_comm]
  exact (Wrench.pair_eq_coordinates_dotProduct F (c.bodyJacobian θ i)).symm

/-- **MLS printed pp. 62–63, eqs. (2.65)–(2.67), with p. 121, eqs. (3.59)–(3.60).** The two
forms of the force pullback agree: the spatial pullback (3.60) of the spatial wrench
`Wrench.transform (c.fk θ) F_t`, the body wrench `F_t` moved to the spatial frame (the
inverse of eq. (2.67), `F_b = Ad_gᵀ F_s`), equals the body pullback (3.59) of `F_t`. Wrench
`(f, τ)`, twist `(v, ω)`, Lean column `i` = book column `i + 1`. -/
theorem spatialWrenchTorques_transform (c : SerialChain n) (θ : Fin n → ℝ) (F : Wrench) :
    c.spatialWrenchTorques θ (Wrench.transform (c.fk θ) F) = c.bodyWrenchTorques θ F := by
  funext i
  simp only [spatialWrenchTorques, bodyWrenchTorques]
  rw [spatialJacobian_eq_adjoint_bodyJacobian, Wrench.pair_transform_adjoint]

/-- **MLS printed pp. 62–63, eq. (2.67), with p. 121, eqs. (3.59)–(3.60).** The body
pullback (3.59) of the body wrench `Wrench.transform (c.fk θ)⁻¹ F_s` (eq. (2.67),
`F_b = Ad_gᵀ F_s`) equals the spatial pullback (3.60) of the spatial wrench `F_s`. Wrench
`(f, τ)`, twist `(v, ω)`, Lean column `i` = book column `i + 1`. -/
theorem bodyWrenchTorques_transform_inv (c : SerialChain n) (θ : Fin n → ℝ) (F : Wrench) :
    c.bodyWrenchTorques θ (Wrench.transform (c.fk θ)⁻¹ F) = c.spatialWrenchTorques θ F := by
  funext i
  simp only [spatialWrenchTorques, bodyWrenchTorques]
  rw [bodyJacobian_eq_adjoint_inv_spatialJacobian, Wrench.pair_transform_adjoint]

end SerialChain

end RoboLean
