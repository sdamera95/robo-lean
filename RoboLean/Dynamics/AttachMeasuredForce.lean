import RoboLean.Control.RobotAttach

/-!
# The net force on the payload of an attached robot (MLS p. 305)

MLS Chapter 6, §5.2, printed p. 305: "To read the configuration of the composite robot, we query
the state of all the robots in the list of daughter robots and then solve the (holonomic) constraint
... A similar computation or measurement can be used to determine the net force on the object,
which will consist of contact forces applied by the fingers and external forces applied by the
environment."

**Formalized.** For the `attach` operation of the library (fingers `F`, payload `P`, constraint data
`A`, `J` invertible):

* the contact force computed from the fingers, `λ = J⁻ᵀ (τ − M_f θ̈ − C_f θ̇ − N_f)` (the formula of
  p. 280 with the sign of p. 267), as `contactForce`;
* the net force on the payload, `G λ + F_e`, contact forces plus an external force `F_e` applied by
  the environment, as `netForce` (the output of the attached robot that p. 305 describes);
* the attached equations with an external force: the constrained equations of fingers and payload
  with a payload force `F_e`, `∃ λ, M_f θ̈ + C_f θ̇ + N_f + Jᵀ λ = τ ∧ M_p ẍ + C_p ẋ + N_p = G λ + F_e`,
  hold exactly when `M̃ ẍ + C̃ ẋ + Ñ = G J⁻ᵀ τ + F_e` (`attach_equations_external_iff`; `F_e = 0` is
  `RobotSystem.attach_equations_iff`);
* the closed-loop identity: along the attached robot's motion the computed net force equals the
  payload's measured inertial reaction, `G λ + F_e = M_p ẍ + C_p ẋ + N_p`, and conversely
  (`netForce_eq_iff`), so "computation" from the fingers and "measurement" on the payload agree
  exactly on motions of the attached robot.

**Hypotheses MLS does not state**, explicit: `J(x)` invertible (p. 305 assumes it "for the purposes
of exposition"); the external force enters the payload equation additively with no constraint
force of its own. The book's figure-level data flow (Figure 6.11) is not modeled beyond this output.
Nothing here concerns a physical sensor.
-/

noncomputable section

open Matrix
open RoboLean.Composite

namespace RoboLean
namespace Control
namespace RobotSystem

variable {n p : ℕ}

/-- **The contact force computed from the fingers (MLS printed p. 305, "a similar computation ...
can be used to determine the net force on the object", with the contact force formula of p. 280,
sign of p. 267):** `λ = J⁻ᵀ (τ − M_f θ̈ − C_f θ̇ − N_f)` at the fingers' state on the constraint,
`θ = σ(x)`, `θ̇ = J⁻¹ Gᵀ ẋ`, `θ̈ = J⁻¹ Gᵀ ẍ + Bd ẋ`. -/
def contactForce (F : RobotSystem n) (A : AttachConstraint n p) (x v a : Fin p → ℝ)
    (τ : Fin n → ℝ) : Fin n → ℝ :=
  ((A.J x)⁻¹)ᵀ *ᵥ (τ - (F.M (A.σ x) *ᵥ A.fingerAcceleration x v a +
    F.C (A.σ x) (A.fingerVelocity x v) *ᵥ A.fingerVelocity x v +
      F.N (A.σ x) (A.fingerVelocity x v)))

/-- **The net force on the payload (MLS printed p. 305, "the net force on the object, which will
consist of contact forces applied by the fingers and external forces applied by the
environment"):** `G λ + F_e` with `λ = contactForce`. -/
def netForce (F : RobotSystem n) (A : AttachConstraint n p) (x v a : Fin p → ℝ) (τ : Fin n → ℝ)
    (Fe : Fin p → ℝ) : Fin p → ℝ :=
  A.G x *ᵥ contactForce F A x v a τ + Fe

/-- **The constraint force of the finger equation is the computed contact force (MLS p. 280, sign
of p. 267, at the state of p. 305):** with `J(x)` invertible, `M_f θ̈ + C_f θ̇ + N_f + Jᵀ λ = τ`
exactly when `λ = contactForce`. -/
theorem finger_equation_iff_contactForce (F : RobotSystem n) (A : AttachConstraint n p)
    {x v a : Fin p → ℝ} (hJ : IsUnit (A.J x).det) (τ lam : Fin n → ℝ) :
    F.M (A.σ x) *ᵥ A.fingerAcceleration x v a +
        F.C (A.σ x) (A.fingerVelocity x v) *ᵥ A.fingerVelocity x v +
        F.N (A.σ x) (A.fingerVelocity x v) + (A.J x)ᵀ *ᵥ lam = τ ↔
      lam = contactForce F A x v a τ := by
  constructor
  · intro h
    rw [contactForce, ← h, add_sub_cancel_left, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv _ hJ, Matrix.transpose_one, Matrix.one_mulVec]
  · intro h
    rw [h, contactForce, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul _ hJ, Matrix.transpose_one, Matrix.one_mulVec]
    abel

/-- **The attached robot under an external payload force (MLS printed p. 305 with (6.24), p. 280,
sign of p. 267).** At a payload state `(x, v)` with acceleration `a`, the fingers on the constraint
and `J(x)` invertible: there is a constraint force `λ` with `M_f θ̈ + C_f θ̇ + N_f + Jᵀ λ = τ` and
`M_p a + C_p v + N_p = G λ + F_e` exactly when `M̃ a + C̃ v + Ñ = G J⁻ᵀ τ + F_e`. -/
theorem attach_equations_external_iff (F : RobotSystem n) (P : RobotSystem p)
    (A : AttachConstraint n p) {x v a : Fin p → ℝ} (hJ : IsUnit (A.J x).det) (τ : Fin n → ℝ)
    (Fe : Fin p → ℝ) :
    (∃ lam : Fin n → ℝ,
      F.M (A.σ x) *ᵥ A.fingerAcceleration x v a +
          F.C (A.σ x) (A.fingerVelocity x v) *ᵥ A.fingerVelocity x v +
          F.N (A.σ x) (A.fingerVelocity x v) + (A.J x)ᵀ *ᵥ lam = τ ∧
        P.M x *ᵥ a + P.C x v *ᵥ v + P.N x v = A.G x *ᵥ lam + Fe) ↔
      (F.attach P A).M x *ᵥ a + (F.attach P A).C x v *ᵥ v + (F.attach P A).N x v =
        effectiveForce (A.J x) (A.G x) τ + Fe := by
  have key := effective_dynamics_eq (P.M x) (P.C x v) (P.N x v) (F.M (A.σ x))
    (F.C (A.σ x) (A.fingerVelocity x v)) (A.J x) (F.N (A.σ x) (A.fingerVelocity x v)) (A.G x)
    (A.Bd x v) (x' := v) (x'' := a) (θ' := A.fingerVelocity x v)
    (θ'' := A.fingerAcceleration x v a) rfl rfl
  have key' : (F.attach P A).M x *ᵥ a + (F.attach P A).C x v *ᵥ v + (F.attach P A).N x v =
      (P.M x *ᵥ a + P.C x v *ᵥ v + P.N x v) + (A.G x * ((A.J x)⁻¹)ᵀ) *ᵥ
        (F.M (A.σ x) *ᵥ A.fingerAcceleration x v a +
          F.C (A.σ x) (A.fingerVelocity x v) *ᵥ A.fingerVelocity x v +
          F.N (A.σ x) (A.fingerVelocity x v)) :=
    key.symm
  have hc : A.G x *ᵥ contactForce F A x v a τ =
      effectiveForce (A.J x) (A.G x) τ - (A.G x * ((A.J x)⁻¹)ᵀ) *ᵥ
        (F.M (A.σ x) *ᵥ A.fingerAcceleration x v a +
          F.C (A.σ x) (A.fingerVelocity x v) *ᵥ A.fingerVelocity x v +
          F.N (A.σ x) (A.fingerVelocity x v)) := by
    rw [contactForce, effectiveForce, Matrix.mulVec_mulVec, Matrix.mulVec_sub]
  rw [key']
  constructor
  · rintro ⟨lam, h1, h2⟩
    rw [(finger_equation_iff_contactForce F A hJ τ lam).mp h1, hc] at h2
    rw [h2]
    abel
  · intro h
    refine ⟨contactForce F A x v a τ, (finger_equation_iff_contactForce F A hJ τ _).mpr rfl, ?_⟩
    rw [hc, sub_add_eq_add_sub, ← h, add_sub_cancel_right]

/-- **The closed-loop identity of the net-force output (MLS printed p. 305, "a similar computation
or measurement can be used to determine the net force on the object"):** with `J(x)` invertible,
the attached robot's equation under an external force, `M̃ a + C̃ v + Ñ = G J⁻ᵀ τ + F_e`, holds
exactly when the net force computed from the fingers equals the payload's inertial reaction,
`G λ + F_e = M_p a + C_p v + N_p`. -/
theorem netForce_eq_iff (F : RobotSystem n) (P : RobotSystem p) (A : AttachConstraint n p)
    {x v a : Fin p → ℝ} (hJ : IsUnit (A.J x).det) (τ : Fin n → ℝ) (Fe : Fin p → ℝ) :
    (F.attach P A).M x *ᵥ a + (F.attach P A).C x v *ᵥ v + (F.attach P A).N x v =
        effectiveForce (A.J x) (A.G x) τ + Fe ↔
      netForce F A x v a τ Fe = P.M x *ᵥ a + P.C x v *ᵥ v + P.N x v := by
  rw [← attach_equations_external_iff F P A hJ τ Fe, netForce]
  constructor
  · rintro ⟨lam, h1, h2⟩
    rw [h2, (finger_equation_iff_contactForce F A hJ τ lam).mp h1]
  · intro h
    exact ⟨_, (finger_equation_iff_contactForce F A hJ τ _).mpr rfl, h.symm⟩

end RobotSystem
end Control
end RoboLean
