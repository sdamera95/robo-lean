import RoboLean.Dynamics.RigidBodyInertia
import RoboLean.Geometry.Wrench
import RoboLean.Geometry.TwistBracket
import RoboLean.Geometry.RotationPlane
import RoboLean.Geometry.ElementaryRotations
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The Newton–Euler equations of a rigid body in body coordinates

MLS Chapter 4, §2.4, printed pp. 165–167. For a body frame at the mass center, a body velocity
`Vᵇ = (v, ω)` and a wrench `Fᵇ = (f, τ)` applied at the mass center and expressed in the body
frame, the Newton–Euler equation in body coordinates, eq. (4.16) on p. 167, is

`[[m I, 0], [0, 𝓘]] V̇ᵇ + (ω × m v, ω × 𝓘 ω) = Fᵇ`,

combining Newton's law (4.14) and Euler's equation (4.15) in body coordinates.

Contents:

* the body momentum `(m v, 𝓘 ω)`, the gyroscopic term `(ω × m v, ω × 𝓘 ω)`, and the predicate
  `NewtonEulerEquation`, which is eq. (4.16) at one instant, with its split into (4.14) and
  (4.15);
* the coadjoint action `ad_Vᵀ`, the transpose with respect to the pairing of MLS p. 61 of the
  bracket `ad_V η = [V, η]` of eq. (4.26), p. 175 (Appendix A, Example A.8), its six-by-six
  matrix, and the coadjoint form `𝓜 V̇ − ad_Vᵀ (𝓜 V) = F` of (4.16) (a derivation in the
  library's bracket convention, not printed in MLS);
* the predicate `NewtonEuler` of (4.16) along a curve of body velocities with actual
  derivative data, the body-velocity curve of a pose trajectory, and the power balance
  `d/dt T = Fᵇ · Vᵇ` for the kinetic energy of eq. (4.9), p. 162;
* a satisfiability instance: torque-free rotation about a principal axis through the mass
  center.

Equation (4.16) is taken as the definition: the derivation from (4.12)–(4.13) on pp. 166–167
is not formalized. The inertia tensor `𝓘` is any real `3 × 3` matrix; its symmetry, which MLS
builds into the definition on p. 162, is a hypothesis where it is needed. The wrench is applied
at the mass center and expressed in body coordinates; twists are ordered `(v, ω)` and wrenches
`(f, τ)`. Masses, lengths and times carry units only by convention. Nothing here asserts
anything about a physical body.
-/

noncomputable section
open Matrix

namespace RoboLean
namespace RigidBody

/-- The inertia tensor acting on a body angular velocity, `𝓘 ω` (MLS p. 162 and eq. (4.15),
p. 167), as a vector of `Vec3`. `𝓘` is any real `3 × 3` matrix, expressed in the body frame at
the mass center. -/
def inertiaAct (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (ω : Vec3) : Vec3 :=
  WithLp.toLp 2 (𝓘 *ᵥ WithLp.ofLp ω)

/-- The body momentum `(m v, 𝓘 ω)` of a rigid body with body velocity `V = (v, ω)`, the wrench
`𝓜 V` of MLS eq. (4.16), p. 167, at the mass center in body coordinates. Twist order `(v, ω)`,
wrench order `(f, τ)`. -/
def momentum (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (V : Twist) : Wrench :=
  ⟨m • V.linear, inertiaAct 𝓘 V.angular⟩

/-- The six coordinates of the body momentum are the generalized inertia `[[m I, 0], [0, 𝓘]]`
of MLS eq. (4.9), p. 162, applied to the six coordinates of the body velocity, as in the first
term of eq. (4.16), p. 167. Twist order `(v, ω)`, wrench order `(f, τ)`. -/
theorem coordinates_momentum (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (V : Twist) :
    (momentum m 𝓘 V).coordinates = generalizedInertia m 𝓘 *ᵥ V.coordinates := by
  funext i
  rcases i with i | i <;>
    simp [Wrench.coordinates, Twist.coordinates, generalizedInertia, Matrix.fromBlocks_mulVec,
      momentum, inertiaAct, Matrix.smul_mulVec]

/-- The gyroscopic term `(ω × m v, ω × 𝓘 ω)` of MLS eq. (4.16), p. 167, for a body velocity
`V = (v, ω)`, as a wrench at the mass center in body coordinates. Twist order `(v, ω)`, wrench
order `(f, τ)`. -/
def gyroscopic (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (V : Twist) : Wrench :=
  ⟨Vec3.cross V.angular (m • V.linear), Vec3.cross V.angular (inertiaAct 𝓘 V.angular)⟩

/-- The coadjoint action `ad_Vᵀ F = (−ω × f, −v × f − ω × τ)` of a twist `V = (v, ω)` on a
wrench `F = (f, τ)`: the transpose, with respect to the pairing of MLS p. 61, of the bracket
`ad_V η = [V, η]` of MLS eq. (4.26), p. 175 (Appendix A, Example A.8), in the library's bracket
convention `Twist.bracket`. -/
def coadjoint (V : Twist) (F : Wrench) : Wrench :=
  ⟨-Vec3.cross V.angular F.force, -(Vec3.cross V.linear F.force + Vec3.cross V.angular F.torque)⟩

/-- The coadjoint action is the transpose of the bracket `ad_V η = [V, η]` (MLS eq. (4.26),
p. 175; Appendix A, Example A.8) with respect to the pairing `f · v + τ · ω` of MLS p. 61:
`⟨ad_Vᵀ F, η⟩ = ⟨F, [V, η]⟩`. -/
theorem pair_coadjoint (V η : Twist) (F : Wrench) :
    Wrench.pair (coadjoint V F) η = Wrench.pair F (Twist.bracket V η) := by
  simp [Wrench.pair, coadjoint, Twist.bracket, Vec3.cross, cross_apply, PiLp.inner_apply,
    Fin.sum_univ_three]
  ring

/-- The six-by-six matrix `ad_V = [[ω̂, v̂], [0, ω̂]]` of the bracket `ad_V η = [V, η]` of MLS
eq. (4.26), p. 175 (Appendix A, Example A.8), for `V = (v, ω)`, with rows and columns indexed
like `Twist.coordinates` (linear first). -/
def adMatrix (V : Twist) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks (Vec3.hat V.angular) (Vec3.hat V.linear) 0 (Vec3.hat V.angular)

/-- The matrix `[[ω̂, v̂], [0, ω̂]]` acts on six coordinates as the bracket `ad_V η = [V, η]` of
MLS eq. (4.26), p. 175 (Appendix A, Example A.8), in the library's convention
`Twist.bracket`, twist order `(v, ω)`. -/
theorem adMatrix_mulVec (V η : Twist) :
    adMatrix V *ᵥ η.coordinates = (Twist.bracket V η).coordinates := by
  funext i
  rcases i with i | i <;>
    simp [adMatrix, Twist.coordinates, Matrix.fromBlocks_mulVec, Vec3.hat_mulVec,
      Twist.bracket]
  rw [Vec3.cross_anticomm η.angular V.linear]
  simp

/-- In six coordinates the coadjoint action is the transposed matrix `ad_Vᵀ` of the bracket of
MLS eq. (4.26), p. 175 (Appendix A, Example A.8); the transpose is taken with respect to the
pairing of MLS p. 61, which is the dot product of the coordinates `(f, τ)` and `(v, ω)`. -/
theorem coordinates_coadjoint (V : Twist) (F : Wrench) :
    (coadjoint V F).coordinates = (adMatrix V)ᵀ *ᵥ F.coordinates := by
  funext i
  rcases i with i | i <;>
    simp [adMatrix, Wrench.coordinates, Matrix.fromBlocks_transpose, Matrix.fromBlocks_mulVec,
      Matrix.neg_mulVec, Vec3.hat_mulVec, coadjoint]
  exact add_comm _ _

private theorem cross_self (v : Vec3) : Vec3.cross v v = 0 := by
  ext i
  fin_cases i <;> simp [Vec3.cross]

/-- MLS eq. (4.16), p. 167, in coadjoint form `𝓜 V̇ − ad_Vᵀ (𝓜 V) = F`: the gyroscopic term
equals `−ad_Vᵀ` applied to the body momentum, because `v × m v = 0`. This is a derivation in
the library's bracket convention, not printed in MLS. -/
theorem gyroscopic_eq_neg_coadjoint (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (V : Twist) :
    gyroscopic m 𝓘 V = -coadjoint V (momentum m 𝓘 V) := by
  ext1
  · simp [gyroscopic, coadjoint, momentum]
  · simp [gyroscopic, coadjoint, momentum, cross_self]

private theorem coordinates_neg (F : Wrench) : (-F).coordinates = -F.coordinates := by
  funext i
  rcases i with i | i <;> rfl

/-- MLS eq. (4.16), p. 167, in coadjoint form `𝓜 V̇ − ad_Vᵀ (𝓜 V) = F`, in six coordinates:
the gyroscopic term is `−ad_Vᵀ 𝓜 V`, with `𝓜` the generalized inertia of eq. (4.9), p. 162.
This is a derivation in the library's bracket convention, not printed in MLS. -/
theorem coordinates_gyroscopic (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (V : Twist) :
    (gyroscopic m 𝓘 V).coordinates =
      -((adMatrix V)ᵀ *ᵥ (generalizedInertia m 𝓘 *ᵥ V.coordinates)) := by
  rw [gyroscopic_eq_neg_coadjoint, coordinates_neg, coordinates_coadjoint,
    coordinates_momentum]

/-- The gyroscopic term of MLS eq. (4.16), p. 167, does no work on the body velocity: its
pairing (MLS p. 61) with `V` is zero. This is the step of the power balance `d/dt T = Fᵇ · Vᵇ`
for the kinetic energy of eq. (4.9), p. 162, that holds for any `𝓘`. -/
theorem pair_gyroscopic_self (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (V : Twist) :
    Wrench.pair (gyroscopic m 𝓘 V) V = 0 := by
  simp [Wrench.pair, gyroscopic, Vec3.cross, cross_apply, PiLp.inner_apply,
    Fin.sum_univ_three]
  ring

/-- **MLS eq. (4.16), p. 167, at one instant.** The Newton–Euler equation in body coordinates,
`𝓜 A + (ω × m v, ω × 𝓘 ω) = F`, for a body velocity `V = (v, ω)`, a body acceleration `A`
(the derivative of `V`, supplied separately) and a wrench `F` applied at the mass center in
body coordinates. Twist order `(v, ω)`, wrench order `(f, τ)`. -/
def NewtonEulerEquation (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (V A : Twist) (F : Wrench) :
    Prop :=
  momentum m 𝓘 A + gyroscopic m 𝓘 V = F

/-- **MLS eqs. (4.14)–(4.16), p. 167.** The Newton–Euler equation (4.16) holds exactly when
Newton's law in body coordinates, `m v̇ + ω × m v = f` (4.14), and Euler's equation in body
coordinates, `𝓘 ω̇ + ω × 𝓘 ω = τ` (4.15), both hold, for a wrench at the mass center in body
coordinates. Twist order `(v, ω)`, wrench order `(f, τ)`. -/
theorem newtonEulerEquation_iff (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (V A : Twist)
    (F : Wrench) :
    NewtonEulerEquation m 𝓘 V A F ↔
      m • A.linear + Vec3.cross V.angular (m • V.linear) = F.force ∧
        inertiaAct 𝓘 A.angular + Vec3.cross V.angular (inertiaAct 𝓘 V.angular) = F.torque :=
  Wrench.ext_iff

/-- **MLS eq. (4.16), p. 167, along a body-velocity curve.** A curve of body velocities `V`
and a curve of wrenches `F` (at the mass center, in body coordinates) satisfy the Newton–Euler
equation when, at every time, both components of `V` have an actual derivative `A` and
`NewtonEulerEquation` holds with that `A`. Twist order `(v, ω)`, wrench order `(f, τ)`. -/
def NewtonEuler (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (V : ℝ → Twist) (F : ℝ → Wrench) : Prop :=
  ∀ t, ∃ A : Twist, HasDerivAt (fun s => (V s).linear) A.linear t ∧
    HasDerivAt (fun s => (V s).angular) A.angular t ∧ NewtonEulerEquation m 𝓘 (V t) A (F t)

/-- The body velocity curve of a pose trajectory `g`, from actual derivative data `D s` of the
homogeneous pose at every time (`RigidTransform.bodyVelocity`, MLS eq. (2.55)), for use as the
curve `V` of MLS eq. (4.16), p. 167. Twist order `(v, ω)`. -/
def bodyVelocityCurve (g : ℝ → RigidTransform) (D : ℝ → HomogeneousMatrix)
    (hD : ∀ s, HasDerivAt (fun r => (g r).toHomogeneous) (D s) s) : ℝ → Twist :=
  fun s => RigidTransform.bodyVelocity g (D s) s (hD s)

private def inertiaActCLM (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) : Vec3 →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := inertiaAct 𝓘
      map_add' := fun x y => by simp [inertiaAct, Matrix.mulVec_add]
      map_smul' := fun c x => by simp [inertiaAct, Matrix.mulVec_smul] }

private theorem inner_inertiaAct_comm {𝓘 : Matrix (Fin 3) (Fin 3) ℝ} (h𝓘 : 𝓘.IsSymm)
    (x y : Vec3) : inner ℝ x (inertiaAct 𝓘 y) = inner ℝ y (inertiaAct 𝓘 x) := by
  simp only [inertiaAct, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, h𝓘.eq,
    dotProduct_comm]

private theorem kineticEnergy_eq_inner (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (V : Twist) :
    kineticEnergy (generalizedInertia m 𝓘) V =
      (1 / 2 : ℝ) * m * inner ℝ V.linear V.linear +
        (1 / 2 : ℝ) * inner ℝ V.angular (inertiaAct 𝓘 V.angular) := by
  rw [kineticEnergy_generalizedInertia, real_inner_self_eq_norm_sq]
  simp only [inertiaAct, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [dotProduct_comm (𝓘 *ᵥ _)]

/-- **Rate of change of kinetic energy.** For a curve of body velocities `V` with actual
derivative `A` at `t`, the kinetic energy `½ Vᵀ 𝓜 V` of MLS eq. (4.9), p. 162, has derivative
`⟨𝓜 A, V⟩`, the pairing (MLS p. 61) of the body momentum of `A` with `V`. Symmetric `𝓘` is
assumed: MLS defines `𝓘` symmetric, here it is a hypothesis. Twist order `(v, ω)`. -/
theorem hasDerivAt_kineticEnergy {m : ℝ} {𝓘 : Matrix (Fin 3) (Fin 3) ℝ} (h𝓘 : 𝓘.IsSymm)
    {V : ℝ → Twist} {A : Twist} {t : ℝ}
    (hv : HasDerivAt (fun s => (V s).linear) A.linear t)
    (hω : HasDerivAt (fun s => (V s).angular) A.angular t) :
    HasDerivAt (fun s => kineticEnergy (generalizedInertia m 𝓘) (V s))
      (Wrench.pair (momentum m 𝓘 A) (V t)) t := by
  have hI : HasDerivAt (fun s => inertiaAct 𝓘 (V s).angular) (inertiaAct 𝓘 A.angular) t :=
    (inertiaActCLM 𝓘).hasFDerivAt.comp_hasDerivAt t hω
  have h := (((HasDerivAt.inner ℝ hv hv).const_mul (1 / 2 * m)).add
    ((HasDerivAt.inner ℝ hω hI).const_mul (1 / 2 : ℝ)))
  rw [show (fun s => kineticEnergy (generalizedInertia m 𝓘) (V s)) = fun s =>
      1 / 2 * m * inner ℝ (V s).linear (V s).linear +
        1 / 2 * inner ℝ (V s).angular (inertiaAct 𝓘 (V s).angular) from
    funext fun s => kineticEnergy_eq_inner m 𝓘 (V s)]
  convert h using 1
  rw [inner_inertiaAct_comm h𝓘 A.angular (V t).angular, real_inner_comm A.linear (V t).linear]
  simp only [Wrench.pair, momentum, real_inner_smul_left,
    real_inner_comm (V t).angular (inertiaAct 𝓘 A.angular)]
  ring

/-- **Power balance at one instant.** If the body velocity has actual derivative `A` at `t`
and the Newton–Euler equation (4.16) of MLS p. 167 holds there with wrench `F`, then the
kinetic energy of eq. (4.9), p. 162, has derivative `Fᵇ · Vᵇ`, the pairing of MLS p. 61. Symmetric
`𝓘` is assumed: MLS defines `𝓘` symmetric, here it is a hypothesis. -/
theorem hasDerivAt_kineticEnergy_of_newtonEulerEquation {m : ℝ}
    {𝓘 : Matrix (Fin 3) (Fin 3) ℝ} (h𝓘 : 𝓘.IsSymm) {V : ℝ → Twist} {A : Twist} {F : Wrench}
    {t : ℝ} (hv : HasDerivAt (fun s => (V s).linear) A.linear t)
    (hω : HasDerivAt (fun s => (V s).angular) A.angular t)
    (hNE : NewtonEulerEquation m 𝓘 (V t) A F) :
    HasDerivAt (fun s => kineticEnergy (generalizedInertia m 𝓘) (V s)) (Wrench.pair F (V t)) t := by
  have h := hasDerivAt_kineticEnergy (m := m) h𝓘 hv hω
  rwa [← hNE, Wrench.pair_add_left, pair_gyroscopic_self, add_zero]

/-- **Power balance along solutions.** Along a solution of the Newton–Euler equation (4.16) of
MLS p. 167, the kinetic energy of eq. (4.9), p. 162, satisfies `d/dt T = Fᵇ · Vᵇ` at every
time, with the pairing of MLS p. 61. Symmetric `𝓘` is assumed: MLS defines `𝓘` symmetric, here
it is a hypothesis. -/
theorem NewtonEuler.hasDerivAt_kineticEnergy {m : ℝ} {𝓘 : Matrix (Fin 3) (Fin 3) ℝ}
    (h𝓘 : 𝓘.IsSymm) {V : ℝ → Twist} {F : ℝ → Wrench} (h : NewtonEuler m 𝓘 V F) (t : ℝ) :
    HasDerivAt (fun s => kineticEnergy (generalizedInertia m 𝓘) (V s)) (Wrench.pair (F t) (V t))
      t := by
  obtain ⟨A, hv, hω, hNE⟩ := h t
  exact hasDerivAt_kineticEnergy_of_newtonEulerEquation h𝓘 hv hω hNE

/-- **Satisfiability instance for MLS eq. (4.16), p. 167: torque-free rotation about a
principal axis through the mass center** (illustrative; not a printed MLS example). The pose
`exp(ξ s)` with `ξ = (0, e_z)` has constant body velocity `ξ` (from its actual derivative,
MLS eq. (2.55)), so the body acceleration is zero; for a diagonal inertia tensor the gyroscopic
term vanishes and the Newton–Euler equation holds with zero wrench, for every mass `m`. -/
theorem newtonEuler_exp_zAxis (m : ℝ) (d : Fin 3 → ℝ) :
    NewtonEuler m (Matrix.diagonal d)
      (bodyVelocityCurve (fun s => Twist.exp ⟨0, Rotation.zAxis⟩ s * 1)
        (fun s => ((1 : ℝ) • (⟨0, Rotation.zAxis⟩ : Twist).hat) *
          (Twist.exp ⟨0, Rotation.zAxis⟩ s * 1).toHomogeneous)
        (fun s => RigidTransform.hasDerivAt_toHomogeneous_exp_mul ⟨0, Rotation.zAxis⟩ 1
          (hasDerivAt_id s)))
      (fun _ => 0) := by
  have hV : bodyVelocityCurve (fun s => Twist.exp ⟨0, Rotation.zAxis⟩ s * 1)
        (fun s => ((1 : ℝ) • (⟨0, Rotation.zAxis⟩ : Twist).hat) *
          (Twist.exp ⟨0, Rotation.zAxis⟩ s * 1).toHomogeneous)
        (fun s => RigidTransform.hasDerivAt_toHomogeneous_exp_mul ⟨0, Rotation.zAxis⟩ 1
          (hasDerivAt_id s)) = fun _ => ⟨0, Rotation.zAxis⟩ := by
    funext s
    refine (RigidTransform.bodyVelocity_exp_mul ⟨0, Rotation.zAxis⟩ 1 (hasDerivAt_id s)).trans ?_
    simp
  rw [hV]
  intro t
  refine ⟨0, hasDerivAt_const t _, hasDerivAt_const t _, ?_⟩
  rw [newtonEulerEquation_iff]
  constructor <;> ext i <;> fin_cases i <;>
    simp [inertiaAct, Vec3.cross, cross_apply, Rotation.zAxis, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

end RigidBody
end RoboLean
