import RoboLean.Dynamics.CompositeDynamics
import RoboLean.Dynamics.NewtonEuler
import RoboLean.Geometry.RigidVelocity

/-!
# Object dynamics in local coordinates: Exercise 4 and a chart of the object pose (MLS §6.2)

MLS Chapter 6, §2.1, printed pp. 276–277, eq. (6.17), and Exercise 4, p. 314 (renders inspected this
session).

**What MLS states.** The object obeys the Newton–Euler equations
`[[mI, 0], [0, 𝓘]] V̇ᵇ + (ωᵇ × m vᵇ, ωᵇ × 𝓘 ωᵇ) = Fᵇ` (p. 276; Exercise 4) at its center of mass;
with gravity alone the book writes (6.17) with the Coriolis block
`[[m ω̂ᵇ, 0], [0, ½(ω̂ᵇ 𝓘 − 𝓘 ω̂ᵇ)]]` (p. 277). "Letting `x ∈ ℝ⁶` be a local parameterization for
`x_o ∈ SE(3)`, the object dynamics can be written as `M_o(x) ẍ + C_o(x, ẋ) ẋ + N_o(x, ẋ) = 0` ... It
can be shown that `M_o(x) > 0` and `Ṁ_o − 2C_o` is skew-symmetric (see Exercise 4)." Exercise 4 (p.
314): (a) the Newton–Euler equations can be written `M V̇ᵇ + C Vᵇ = Fᵇ` with `M > 0` and `Ṁ − 2C`
skew; (b) for a local parameterization `x_o = φ(x)` with `J(x) = [(φ⁻¹ ∂φ/∂x₁)^∨ ⋯ (φ⁻¹ ∂φ/∂x₆)^∨]`
nonsingular, the equations become `M̄(x) ẍ + C̄(x, ẋ) ẋ = Jᵀ(x) Fᵇ` with `M̄ = Jᵀ M J`,
`C̄ = Jᵀ C J + Jᵀ M J̇` (printed with a doubled `+ +`).

**Formalized.**

* Exercise 4(a): `objectCoriolis m 𝓘 V = [[m ω̂, 0], [0, −(𝓘ω)^]]`, with `C(V) V` the gyroscopic
  term (`objectCoriolis_mulVec`) and `C(V)` skew-symmetric (`objectCoriolis_transpose`); the
  generalized inertia is constant in body coordinates, so `Ṁ − 2C = −2C` is skew
  (`skew_zero_sub_two_objectCoriolis`), and the Newton–Euler equation is `M V̇ + C(V) V = F`
  (`newtonEulerEquation_iff_coordinates`). The printed (6.17) block is not used: it is symmetric and
  gives half the gyroscopic term (E034 observation O2); the corrected (6.17) is
  `newtonEulerEquation_gravity_iff`.
* A chart of the object pose: `IsBodyJacobian φ Jφ`, a hypothesis structure (the style of
  `IsStateTransition`): along every motion `x` with velocity `ẋ` the pose curve `φ ∘ x` has a
  derivative and its body velocity is `Jφ(x) ẋ`. Column `i` of `Jφ(x)` is then the book's
  `(φ⁻¹ ∂φ/∂xᵢ)^∨` (`IsBodyJacobian.mulVec_single`). Instance with the hypotheses discharged: the
  translational chart `x ↦ (I, x)` (`translationalChart`, `isBodyJacobian_translationalChart`).
* Exercise 4(b): `chartMass Mb Jφ = Jφᵀ Mb Jφ`, `chartCoriolis Mb Cb Jφ Jd = Jφᵀ Cb Jφ + Jφᵀ Mb Jd`;
  along a motion, Newton–Euler gives `M̄ ẍ + C̄ ẋ = Jφᵀ Fᵇ`, and the converse holds when `Jφ` is
  onto (the book's "nonsingular") (`newtonEulerEquation_chart_iff`); `M̄ > 0` for `Jφ` injective
  (`chartMass_posDef`); `M̄˙ − 2C̄` is skew for every actual derivative along a motion
  (`skew_deriv_chartMass_sub_two_chartCoriolis`), by the congruence `Control.skew_reduced`.

These give the "usual structural properties" of `(M_o, C_o)` taken as hypotheses by Lemma 6.1(2)
(`CompositeDynamics`), for this choice of `C_o`. Twist order `(v, ω)`, wrench order `(f, τ)`, six
coordinates `Twist.coordinates`, `Wrench.coordinates`. Nothing here concerns a physical body beyond
the rigid-body model of Chapter 4.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Composite

/-! ### Exercise 4(a): a skew-symmetric Coriolis matrix for the Newton–Euler equations -/

/-- **A Coriolis matrix for the Newton–Euler equations (MLS Exercise 4(a), printed p. 314):**
`C(V) = [[m ω̂, 0], [0, −(𝓘 ω)^]]` for the body velocity `V = (v, ω)`, so that
`C(V) V = (ω × m v, ω × 𝓘 ω)`. It replaces the block `½(ω̂ᵇ 𝓘 − 𝓘 ω̂ᵇ)` printed in (6.17), p. 277
(E034 observation O2). -/
def objectCoriolis (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (V : Twist) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks (m • Vec3.hat V.angular) 0 0 (-Vec3.hat (RigidBody.inertiaAct 𝓘 V.angular))

/-- **MLS Exercise 4(a), p. 314: `C(V) V` is the gyroscopic term `(ω × m v, ω × 𝓘 ω)`** of the
Newton–Euler equations (MLS eq. (4.16), p. 167), in six coordinates. -/
theorem objectCoriolis_mulVec (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (V : Twist) :
    objectCoriolis m 𝓘 V *ᵥ V.coordinates = (RigidBody.gyroscopic m 𝓘 V).coordinates := by
  funext r
  rcases r with i | i
  · simp [objectCoriolis, Twist.coordinates, Wrench.coordinates, RigidBody.gyroscopic,
      Matrix.fromBlocks_mulVec, Matrix.smul_mulVec, Vec3.hat_mulVec]
  · simp [objectCoriolis, Twist.coordinates, Wrench.coordinates, RigidBody.gyroscopic,
      Matrix.fromBlocks_mulVec, Matrix.neg_mulVec, Vec3.hat_mulVec]
    rw [Vec3.cross_anticomm]
    simp

/-- **MLS Exercise 4(a), p. 314: the Coriolis matrix `C(V)` is skew-symmetric.** -/
theorem objectCoriolis_transpose (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (V : Twist) :
    (objectCoriolis m 𝓘 V)ᵀ = -objectCoriolis m 𝓘 V := by
  simp [objectCoriolis, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

/-- **MLS Exercise 4(a), p. 314: "`Ṁ − 2C` is a skew-symmetric matrix"** in body coordinates, where
the generalized inertia `M = [[mI, 0], [0, 𝓘]]` is constant (`Ṁ = 0`). -/
theorem skew_zero_sub_two_objectCoriolis (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (V : Twist) :
    ((0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) - (2 : ℝ) • objectCoriolis m 𝓘 V)ᵀ =
      -((0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) - (2 : ℝ) • objectCoriolis m 𝓘 V) := by
  rw [Matrix.transpose_sub, Matrix.transpose_zero, Matrix.transpose_smul,
    objectCoriolis_transpose]
  simp

/-- **MLS Exercise 4(a), p. 314: "the Newton–Euler equations can be written as
`M(x_o) V̇ᵇ + C(x_o, ẋ_o) Vᵇ = Fᵇ`"**, with `M = [[mI, 0], [0, 𝓘]]` (`generalizedInertia`, positive
definite for `m > 0`, `𝓘 > 0`: `RigidBody.generalizedInertia_posDef`) and `C = objectCoriolis`; the
body acceleration `A` is the twist of derivatives of `V` (E012). -/
theorem newtonEulerEquation_iff_coordinates (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ)
    (V A : Twist) (F : Wrench) :
    RigidBody.NewtonEulerEquation m 𝓘 V A F ↔
      RigidBody.generalizedInertia m 𝓘 *ᵥ A.coordinates +
          objectCoriolis m 𝓘 V *ᵥ V.coordinates = F.coordinates := by
  rw [RigidBody.NewtonEulerEquation, ← Wrench.coordinatesEquiv.injective.eq_iff, map_add]
  simp only [Wrench.coordinatesEquiv_apply, RigidBody.coordinates_momentum,
    objectCoriolis_mulVec]

/-- **MLS eq. (6.17), p. 277, with the Coriolis matrix of Exercise 4(a):** for an object "subject to
gravity alone", with `g⃗` "a vector in the direction of gravity" and orientation `R`, the
Newton–Euler equations with the body wrench `Fᵇ = (−Rᵀ(m g⃗), 0)` hold exactly when
`M V̇ᵇ + C(Vᵇ) Vᵇ + (Rᵀ(m g⃗), 0) = 0`. -/
theorem newtonEulerEquation_gravity_iff (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (V A : Twist)
    (R : Rotation) (g : Vec3) :
    RigidBody.NewtonEulerEquation m 𝓘 V A ⟨-(R⁻¹.act (m • g)), 0⟩ ↔
      RigidBody.generalizedInertia m 𝓘 *ᵥ A.coordinates +
          objectCoriolis m 𝓘 V *ᵥ V.coordinates +
          (Wrench.mk (R⁻¹.act (m • g)) 0).coordinates = 0 := by
  have hF : (⟨-(R⁻¹.act (m • g)), 0⟩ : Wrench).coordinates =
      -(Wrench.mk (R⁻¹.act (m • g)) 0).coordinates := by
    funext r
    rcases r with i | i <;> simp [Wrench.coordinates]
  rw [newtonEulerEquation_iff_coordinates, hF, eq_neg_iff_add_eq_zero]

/-! ### A chart of the object pose (MLS p. 277; Exercise 4(b), p. 314) -/

variable {p : ℕ}

/-- **A body-velocity Jacobian of a chart of the object pose (MLS Exercise 4(b), printed p. 314,
`J(x) = [(φ⁻¹ ∂φ/∂x₁)^∨ ⋯]`), as a hypothesis structure:** `φ : ℝᵖ → SE(3)` is a local
parameterization `x_o = φ(x)` and `Jφ(x) ∈ ℝ^{6×p}` (rows in twist order `(v, ω)`); along every
motion `x` with velocity `ẋ` at `t`, the pose curve `φ ∘ x` has a derivative at `t`, and its body
velocity (MLS eq. (2.60)) is `Jφ(x(t)) ẋ`. Column `i` of `Jφ(x)` is then the book's `(φ⁻¹ ∂φ/∂xᵢ)^∨`
(`IsBodyJacobian.mulVec_single`). -/
structure IsBodyJacobian (φ : (Fin p → ℝ) → RigidTransform)
    (Jφ : (Fin p → ℝ) → Matrix (Fin 3 ⊕ Fin 3) (Fin p) ℝ) : Prop where
  /-- The pose curve `φ ∘ x` has a derivative along every motion. -/
  exists_hasDerivAt : ∀ {x : ℝ → Fin p → ℝ} {x' : Fin p → ℝ} {t : ℝ}, HasDerivAt x x' t →
    ∃ D : HomogeneousMatrix, HasDerivAt (fun s => (φ (x s)).toHomogeneous) D t
  /-- The body velocity of `φ ∘ x` is `Jφ(x) ẋ` (MLS Exercise 4(b), p. 314). -/
  bodyVelocity_eq : ∀ {x : ℝ → Fin p → ℝ} {x' : Fin p → ℝ} {t : ℝ} {D : HomogeneousMatrix},
    HasDerivAt x x' t → ∀ hD : HasDerivAt (fun s => (φ (x s)).toHomogeneous) D t,
      (RigidTransform.bodyVelocity (fun s => φ (x s)) D t hD).coordinates = Jφ (x t) *ᵥ x'

/-- **Column `i` of the chart Jacobian is `(φ⁻¹ ∂φ/∂xᵢ)^∨` (MLS Exercise 4(b), p. 314):** it is the
body velocity of the pose along the coordinate line `s ↦ φ(x + s eᵢ)` at `s = 0`. -/
theorem IsBodyJacobian.mulVec_single {φ : (Fin p → ℝ) → RigidTransform}
    {Jφ : (Fin p → ℝ) → Matrix (Fin 3 ⊕ Fin 3) (Fin p) ℝ} (h : IsBodyJacobian φ Jφ)
    (x : Fin p → ℝ) (i : Fin p) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (φ (x + s • Pi.single i 1)).toHomogeneous) D 0) :
    Jφ x *ᵥ Pi.single i 1 =
      (RigidTransform.bodyVelocity (fun s => φ (x + s • Pi.single i 1)) D 0 hD).coordinates := by
  have hx : HasDerivAt (fun s : ℝ => x + s • Pi.single i (1 : ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ))).const_add x
  rw [h.bodyVelocity_eq hx hD, zero_smul, add_zero]

/-- **The translational chart `x ↦ (I, x)` of the object pose (MLS p. 277, a local parameterization
of the translations in `SE(3)`):** the object keeps the identity orientation and its position is
`x ∈ ℝ³`. -/
def translationalChart (x : Fin 3 → ℝ) : RigidTransform :=
  ⟨1, WithLp.toLp 2 x⟩

/-- **The body-velocity Jacobian of the translational chart (MLS Exercise 4(b), p. 314):**
`[[I], [0]] ∈ ℝ^{6×3}`, the body velocity of `(I, x(t))` being `(ẋ, 0)`. -/
def translationalChartJacobian (_x : Fin 3 → ℝ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3) ℝ :=
  Matrix.of fun r j => Sum.elim (fun i => if i = j then 1 else 0) (fun _ => 0) r

/-- The pose curve `t ↦ (I, x(t))` of the translational chart has the derivative `[[0, ẋ], [0, 0]]`
(MLS eq. (2.60), p. 55, with a constant rotation). -/
private theorem hasDerivAt_translationalChart {x : ℝ → Fin 3 → ℝ} {x' : Fin 3 → ℝ} {t : ℝ}
    (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s => (translationalChart (x s)).toHomogeneous)
      (Matrix.fromBlocks 0 (Matrix.of fun i _ => x' i) 0 0) t := by
  have hx' := hasDerivAt_pi.mp hx
  refine hasDerivAt_pi.mpr fun r => hasDerivAt_pi.mpr fun c => ?_
  rcases r with i | i <;> rcases c with j | j
  · simpa [translationalChart, RigidTransform.toHomogeneous] using
      hasDerivAt_const t ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
  · simpa [translationalChart, RigidTransform.toHomogeneous] using hx' i
  · simpa [translationalChart, RigidTransform.toHomogeneous] using hasDerivAt_const t (0 : ℝ)
  · simpa [translationalChart, RigidTransform.toHomogeneous] using
      hasDerivAt_const t ((1 : Matrix (Fin 1) (Fin 1) ℝ) i j)

/-- **The translational chart satisfies the chart hypothesis (MLS Exercise 4(b), p. 314):** along
every motion `x` with velocity `ẋ`, `t ↦ (I, x(t))` has a derivative and body velocity `(ẋ, 0)`. -/
theorem isBodyJacobian_translationalChart :
    IsBodyJacobian translationalChart translationalChartJacobian := by
  refine ⟨fun {x x' t} hx => ⟨_, hasDerivAt_translationalChart hx⟩, fun {x x' t D} hx hD => ?_⟩
  have hDD : D = Matrix.fromBlocks 0 (Matrix.of fun i _ => x' i) 0 0 := by
    have h0 := hasDerivAt_translationalChart hx
    ext r c
    exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hD r) c).unique
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp h0 r) c)
  subst hDD
  funext r
  rcases r with i | i
  · simp [Twist.coordinates, translationalChart, RigidTransform.translationDerivative,
      translationalChartJacobian, Matrix.mulVec, dotProduct]
  · have key : ∀ ω : Vec3, Vec3.hat ω = 0 → ω = 0 := fun ω h => by
      rw [← Vec3.vee_hat ω, h]
      ext k
      fin_cases k <;> rfl
    have hω0 : (RigidTransform.bodyVelocity (fun s => translationalChart (x s))
        (Matrix.fromBlocks 0 (Matrix.of fun i _ => x' i) 0 0) t hD).angular = 0 :=
      key _ (by simp [RigidTransform.bodyVelocity, translationalChart])
    simp only [Twist.coordinates, Sum.elim_inr, hω0]
    simp [translationalChartJacobian, Matrix.mulVec, dotProduct]

/-! ### Exercise 4(b): the object dynamics in local coordinates -/

/-- **MLS Exercise 4(b), printed p. 314: `M̄ = Jᵀ M J`**, for a `6 × 6` body inertia `Mb` and a
chart Jacobian `Jφ ∈ ℝ^{6×p}`. -/
def chartMass (Mb : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ)
    (Jφ : Matrix (Fin 3 ⊕ Fin 3) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Jφᵀ * Mb * Jφ

/-- **MLS Exercise 4(b), printed p. 314: `C̄ = Jᵀ C J + Jᵀ M J̇`**, with `Jd` standing for `J̇` (an
actual derivative of `s ↦ Jφ(x(s))` where used). -/
def chartCoriolis (Mb Cb : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ)
    (Jφ Jd : Matrix (Fin 3 ⊕ Fin 3) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Jφᵀ * Cb * Jφ + Jφᵀ * Mb * Jd

/-- **The algebra of MLS Exercise 4(b), p. 314:** if `V = Jφ ẋ` and `V̇ = J̇φ ẋ + Jφ ẍ`, then
`Jφᵀ (M V̇ + C V) = M̄ ẍ + C̄ ẋ`. -/
theorem chart_dynamics_eq (Mb Cb : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ)
    (Jφ Jd : Matrix (Fin 3 ⊕ Fin 3) (Fin p) ℝ) {V A : Fin 3 ⊕ Fin 3 → ℝ} {x' x'' : Fin p → ℝ}
    (hV : V = Jφ *ᵥ x') (hA : A = Jd *ᵥ x' + Jφ *ᵥ x'') :
    Jφᵀ *ᵥ (Mb *ᵥ A + Cb *ᵥ V) = chartMass Mb Jφ *ᵥ x'' + chartCoriolis Mb Cb Jφ Jd *ᵥ x' := by
  subst hV hA
  simp only [chartMass, chartCoriolis, Matrix.mulVec_add, Matrix.add_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]
  abel

/-- The product rule for a matrix curve applied to a vector curve, for any finite index types (the
step `V̇ = J̇ ẋ + J ẍ` of MLS Exercise 4(b), p. 314). -/
private theorem hasDerivAt_mulVec_of_entries {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : ℝ → Matrix ι κ ℝ} {A' : Matrix ι κ ℝ} {b : ℝ → κ → ℝ} {b' : κ → ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => A s *ᵥ b s) (A' *ᵥ b t + A t *ᵥ b') t := by
  have hb' := hasDerivAt_pi.mp hb
  refine hasDerivAt_pi.mpr fun i => ?_
  have h : HasDerivAt (fun s => ∑ j, A s i j * b s j)
      (∑ j, (A' i j * b t j + A t i j * b' j)) t :=
    HasDerivAt.fun_sum fun j _ => (hA i j).mul (hb' j)
  simpa [Matrix.mulVec, dotProduct, Finset.sum_add_distrib] using h

/-- A matrix `G` that is onto has an injective transpose, for any finite index types (the converse
direction of MLS Exercise 4(b), p. 314, for a nonsingular `J`). -/
private theorem transpose_mulVec_injective {ι κ : Type*} [Fintype ι] [Fintype κ]
    {G : Matrix ι κ ℝ} (hG : Function.Surjective G.mulVec) : Function.Injective Gᵀ.mulVec := by
  intro a b hab
  have h0 : Gᵀ *ᵥ (a - b) = 0 := by
    rw [Matrix.mulVec_sub]
    exact sub_eq_zero.mpr hab
  obtain ⟨z, hz⟩ := hG (a - b)
  have h1 : (a - b) ⬝ᵥ (G *ᵥ z) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h0, zero_dotProduct]
  rw [hz] at h1
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp h1)

/-- **MLS Exercise 4(b), p. 314: "show that the equations of motion become
`M̄(x) ẍ + C̄(x, ẋ) ẋ = Jᵀ(x) Fᵇ`", along a motion.** Let `Jφ` be a body-velocity Jacobian of the
chart `φ`, `x` a motion with velocity `x'` near `t` and acceleration `x''` at `t`, `V(s)` the body
velocity of `φ ∘ x` near `t` (with the derivatives `D s` of the pose), `A` the body acceleration at
`t` (its coordinates the derivative of those of `V` at `t`), and `Jd` the derivative of
`s ↦ Jφ(x(s))` at `t`. Then the Newton–Euler equation at `t` implies `M̄ ẍ + C̄ ẋ = Jφᵀ Fᵇ` with
`M = [[mI, 0], [0, 𝓘]]` and `C` of Exercise 4(a), and the converse holds when `Jφ(x(t))` is onto
(the book's "nonsingular" `J(x) ∈ ℝ^{6×6}`). -/
theorem newtonEulerEquation_chart_iff {φ : (Fin p → ℝ) → RigidTransform}
    {Jφ : (Fin p → ℝ) → Matrix (Fin 3 ⊕ Fin 3) (Fin p) ℝ} (hφ : IsBodyJacobian φ Jφ)
    (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) {x x' : ℝ → Fin p → ℝ} {x'' : Fin p → ℝ}
    {D : ℝ → HomogeneousMatrix} {A : Twist} {Jd : Matrix (Fin 3 ⊕ Fin 3) (Fin p) ℝ} {t : ℝ}
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (x' s) s) (hx' : HasDerivAt x' x'' t)
    (hD : ∀ s, HasDerivAt (fun r => (φ (x r)).toHomogeneous) (D s) s)
    (hA : HasDerivAt (fun s => (RigidTransform.bodyVelocity (fun r => φ (x r)) (D s) s
      (hD s)).coordinates) A.coordinates t)
    (hJd : ∀ i j, HasDerivAt (fun s => Jφ (x s) i j) (Jd i j) t) (F : Wrench) :
    (RigidBody.NewtonEulerEquation m 𝓘
        (RigidTransform.bodyVelocity (fun r => φ (x r)) (D t) t (hD t)) A F →
      chartMass (RigidBody.generalizedInertia m 𝓘) (Jφ (x t)) *ᵥ x'' +
          chartCoriolis (RigidBody.generalizedInertia m 𝓘)
            (objectCoriolis m 𝓘 (RigidTransform.bodyVelocity (fun r => φ (x r)) (D t) t (hD t)))
            (Jφ (x t)) Jd *ᵥ x' t = (Jφ (x t))ᵀ *ᵥ F.coordinates) ∧
    (Function.Surjective (Jφ (x t)).mulVec →
      (chartMass (RigidBody.generalizedInertia m 𝓘) (Jφ (x t)) *ᵥ x'' +
          chartCoriolis (RigidBody.generalizedInertia m 𝓘)
            (objectCoriolis m 𝓘 (RigidTransform.bodyVelocity (fun r => φ (x r)) (D t) t (hD t)))
            (Jφ (x t)) Jd *ᵥ x' t = (Jφ (x t))ᵀ *ᵥ F.coordinates →
        RigidBody.NewtonEulerEquation m 𝓘
          (RigidTransform.bodyVelocity (fun r => φ (x r)) (D t) t (hD t)) A F)) := by
  have hev : ∀ᶠ s in 𝓝 t, (RigidTransform.bodyVelocity (fun r => φ (x r)) (D s) s
      (hD s)).coordinates = Jφ (x s) *ᵥ x' s :=
    hx.mono fun s hs => hφ.bodyVelocity_eq hs (hD s)
  have hprod := hasDerivAt_mulVec_of_entries (A := fun s => Jφ (x s)) hJd hx'
  have hAt : A.coordinates = Jd *ᵥ x' t + Jφ (x t) *ᵥ x'' :=
    hA.unique (hprod.congr_of_eventuallyEq hev)
  have key := chart_dynamics_eq (RigidBody.generalizedInertia m 𝓘)
    (objectCoriolis m 𝓘 (RigidTransform.bodyVelocity (fun r => φ (x r)) (D t) t (hD t)))
    (Jφ (x t)) Jd hev.self_of_nhds hAt
  rw [newtonEulerEquation_iff_coordinates, ← key]
  exact ⟨fun h => by rw [h], fun hs h => transpose_mulVec_injective hs h⟩

/-- **MLS p. 277: "`M_o(x) > 0`" (Exercise 4(b), p. 314):** `M̄ = Jφᵀ M Jφ` is positive definite for
`M` positive definite and `Jφ` injective (for example a nonsingular `J(x) ∈ ℝ^{6×6}`). -/
theorem chartMass_posDef {Mb : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ}
    {Jφ : Matrix (Fin 3 ⊕ Fin 3) (Fin p) ℝ} (hMb : Mb.PosDef) (hJ : Function.Injective Jφ.mulVec) :
    (chartMass Mb Jφ).PosDef := by
  have h := hMb.conjTranspose_mul_mul_same hJ
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The product rule for two matrix curves, entry by entry, for any finite inner index type (the
derivative `J̇ᵀ M J + Jᵀ M J̇` of MLS Exercise 4(b), p. 314). -/
private theorem hasDerivAt_mul_entry {ι κ μ : Type*} [Fintype κ] {A : ℝ → Matrix ι κ ℝ}
    {B : ℝ → Matrix κ μ ℝ} {A' : Matrix ι κ ℝ} {B' : Matrix κ μ ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t) (i : ι) (k : μ) :
    HasDerivAt (fun s => (A s * B s) i k) ((A' * B t + A t * B') i k) t := by
  have h : HasDerivAt (fun s => ∑ j, A s i j * B s j k)
      (∑ j, (A' i j * B t j k + A t i j * B' j k)) t :=
    HasDerivAt.fun_sum fun j _ => (hA i j).mul (hB j k)
  simpa [Matrix.mul_apply, Finset.sum_add_distrib] using h

/-- **MLS p. 277: "`Ṁ_o − 2C_o` is skew-symmetric (see Exercise 4)", along a motion.** If the
entries of `s ↦ Jφ(s)` have the derivatives `Jd` at `t`, the body inertia `Mb` is symmetric and
constant, and `Cb` is skew-symmetric (`objectCoriolis_transpose`), then every actual derivative
`M̄˙` of `s ↦ Jφ(s)ᵀ Mb Jφ(s)` at `t` makes `M̄˙ − 2C̄` skew-symmetric. -/
theorem skew_deriv_chartMass_sub_two_chartCoriolis
    {Mb Cb : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ} {Jφ : ℝ → Matrix (Fin 3 ⊕ Fin 3) (Fin p) ℝ}
    {Jd : Matrix (Fin 3 ⊕ Fin 3) (Fin p) ℝ} {t : ℝ} (hMb : Mbᵀ = Mb) (hCb : Cbᵀ = -Cb)
    (hJ : ∀ i j, HasDerivAt (fun s => Jφ s i j) (Jd i j) t) {Mtd : Matrix (Fin p) (Fin p) ℝ}
    (hMt : ∀ i j, HasDerivAt (fun s => chartMass Mb (Jφ s) i j) (Mtd i j) t) :
    (Mtd - (2 : ℝ) • chartCoriolis Mb Cb (Jφ t) Jd)ᵀ =
      -(Mtd - (2 : ℝ) • chartCoriolis Mb Cb (Jφ t) Jd) := by
  have hT : ∀ i j, HasDerivAt (fun s => (Jφ s)ᵀ i j) (Jdᵀ i j) t := fun i j => hJ j i
  have hM : ∀ i j, HasDerivAt (fun _ : ℝ => Mb i j) ((0 : Matrix _ _ ℝ) i j) t :=
    fun i j => hasDerivAt_const t (Mb i j)
  have h1 := hasDerivAt_mul_entry (A := fun s => (Jφ s)ᵀ) (B := fun _ => Mb) hT hM
  have h2 := hasDerivAt_mul_entry (A := fun s => (Jφ s)ᵀ * Mb) h1 hJ
  have hMtd : Mtd = Jdᵀ * Mb * Jφ t + (Jφ t)ᵀ * Mb * Jd := by
    ext i j
    rw [(hMt i j).unique (h2 i j)]
    simp
  have hs : ((0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) - (2 : ℝ) • Cb)ᵀ =
      -(0 - (2 : ℝ) • Cb) := by
    rw [Matrix.transpose_sub, Matrix.transpose_zero, Matrix.transpose_smul, hCb]
    simp
  have key := Control.skew_reduced (S := Jφ t) (S' := Jd) hMb hs
  have heq : Mtd - (2 : ℝ) • chartCoriolis Mb Cb (Jφ t) Jd =
      Jdᵀ * Mb * Jφ t + (Jφ t)ᵀ * (0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) * Jφ t +
        (Jφ t)ᵀ * Mb * Jd -
        (2 : ℝ) • ((Jφ t)ᵀ * (Cb * Jφ t + Mb * Jd)) := by
    rw [hMtd, chartCoriolis]
    simp [Matrix.mul_add, Matrix.mul_assoc]
  rw [heq]
  exact key

end Composite
end RoboLean
