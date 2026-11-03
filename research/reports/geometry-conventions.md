# Geometry conventions for RoboLean

Initially recorded 2026-10-09 00:29:36 UTC. This document specifies the rigid-transform,
twist, velocity, and wrench conventions and identifies the checked subset. Implementation
evidence belongs in the [coverage ledger](mls-coverage-ledger.md); this document
alone does not certify a Lean implementation or a physical model.

The source is Murray, Li, and Sastry, MLS, Chapter 2.
References use printed pages; PDF page numbers are 18 larger. The cited formula
pages were read as text and inspected as rendered images, as recorded below.

## Coordinates, frames, and composition

Coordinates are column vectors in a right-handed orthonormal basis, ordered
`x, y, z`. For frames A and B:

- `R_AB` has the axes of B, expressed in A, as its columns.
- `p_AB` is the displacement from A's origin to B's origin, expressed in A.
- `g_AB` converts coordinates of a fixed point from B to A:
  `q_A = R_AB q_B + p_AB`.

MLS writes the mathematical pair as `g_AB = (p_AB, R_AB)`; the Lean structure
uses named `rotation` and `translation` fields, so no positional pair order
should be inferred from its field order. Sources:
pp.23-25 and
p.35, equations (2.21)-(2.22).

Composition applies the right operand first:

\[
g_{AC}=g_{AB}g_{BC},\qquad
R_{AC}=R_{AB}R_{BC},\qquad
p_{AC}=p_{AB}+R_{AB}p_{BC}.
\]

The inverse reverses the coordinate conversion:

\[
g_{BA}=g_{AB}^{-1},\qquad
R_{BA}=R_{AB}^{\mathsf T},\qquad
p_{BA}=-R_{AB}^{\mathsf T}p_{AB}.
\]

Thus `(g * h).applyPoint q` means `g.applyPoint (h.applyPoint q)`.
Sources: rotation composition (2.3), p.25
and rigid composition/inverse, p.37.

A coordinate conversion describes the same physical point in two frames: this
is the passive interpretation of `g_AB`. The same affine formula can also
describe an active displacement, with both the initial and final coordinates
expressed in one fixed frame A. In that interpretation the point moves. Each
theorem or example must state the intended meaning. MLS distinguishes these
interpretations for the twist exponential on
p.42, equation (2.37); that active
motion acts on an initial pose by left multiplication.

## Rotations, points, and displacement vectors

A rotation satisfies `Rᵀ R = R Rᵀ = I` and `det R = 1`. The positive quarter
turn about `+z` sends `e_x` to `e_y`, `e_y` to `-e_x`, and fixes `e_z`.
This specifies the sign without a viewing-direction ambiguity; it matches
MLS's `R_z` matrix on p.31.
Orientation uses `e_x × e_y = e_z` and hat convention `hat(a) b = a × b`,
as on p.26, equations (2.4)-(2.7).

Point action and displacement-vector action are distinct:

\[
g(q)=Rq+p,\qquad g_*(v)=Rv,\qquad
g(q)-g(r)=g_*(q-r).
\]

Translation affects points but cancels in differences. A point plus a
displacement is a point; the difference of two points is a displacement.
Adding two point-coordinate tuples is arithmetically possible in the initial
representation but has no intrinsic affine meaning. Source:
MLS p.36.

The homogeneous representation is

\[
H(g)=\begin{bmatrix}R&p\\0&1\end{bmatrix},\qquad
\bar q=\begin{bmatrix}q\\1\end{bmatrix},\qquad
\bar v=\begin{bmatrix}v\\0\end{bmatrix}.
\]

The last coordinate distinguishes the actions. The block-matrix bridge
uses index type `Fin 3 ⊕ Fin 1`; a displayed `4 × 4` matrix orders its
coordinates as `x, y, z, homogeneous`. Source:
pp.36-37, equations (2.23)-(2.24).

## First-slice representation and limits

The selected core is `RoboLean.Vec3 := EuclideanSpace ℝ (Fin 3)`,
`RoboLean.Rotation := Matrix.specialOrthogonalGroup (Fin 3) ℝ`, and
`RigidTransform` with `rotation` and `translation` fields. Rotation action
uses the Euclidean linear map corresponding to the matrix. This is a
representation decision; this document does not supply implementation checks.

The cross-product/hat slice retains those coordinates: `Vec3.cross` transports
Mathlib's right-handed coordinate cross product through `WithLp`, `Vec3.hat`
has rows `(0,-v₂,v₁)`, `(v₂,0,-v₀)`, `(-v₁,v₀,0)` in Lean's zero-based
indexing, and `Vec3.vee A` reads `(A₂₁,A₀₂,A₁₀)`. `SkewMatrix3` is the
independent real skew-adjoint matrix type, identified by `Aᵀ = -A`.
**Verified — formal statements:** the I2 build and 85-declaration audit
checks `Rotation.act_cross`, `RigidTransform.applyVector_cross`,
`Vec3.hat_mulVec`, `Vec3.hat_act`, and the real linear equivalence
`Vec3.hatLinearEquiv`. It covers all vectors including zero; `hat_vee` requires
the skew condition. The [ledger](mls-coverage-ledger.md#implementation-evidence-i2) gives the
source mapping and evidence limits.

Lengths mean `‖v‖₂ = sqrt(v_x² + v_y² + v_z²)`; distance means
`dist(q,r) = ‖q-r‖₂`. An unadorned function type `Fin 3 → ℝ` must not
silently supply the norm for a robotics distance theorem. MLS's Euclidean
distance and cross-product preservation targets are Propositions 2.2 and 2.7
on p.26 and
p.38.

Frame indexing was evaluated for this slice and deferred: the minimal core
does not enforce A/B/C compatibility. A future frame-indexed wrapper remains
open. Point and vector coordinates also share `Vec3` initially; distinct action
names carry their intended use. Neither convention prevents mislabelled
measured data.

Scalars are exact mathematical real numbers. Choose one consistent length unit
for coordinates and translations, one time unit for trajectories, and compatible
force/torque units for mechanics; rotation entries are dimensionless and angles
use radians. The core does not enforce units. Real-number results do not give
floating-point error bounds, calibration accuracy, a manifold API, or numerical
execution guarantees. Twist coordinates mix translational and angular
quantities, so any six-coordinate norm must declare its metric and length
scale rather than be treated as a canonical physical norm.

## Exact example for composition and inverse

This independently derived coordinate example uses only integer entries;
trigonometric evaluation and floating-point tolerances are unnecessary. Let

\[
R=\begin{bmatrix}0&-1&0\\1&0&0\\0&0&1\end{bmatrix},\qquad
p=\begin{bmatrix}1\\2\\3\end{bmatrix},\qquad
t=\begin{bmatrix}2\\0\\0\end{bmatrix}.
\]

Let `g` have rotation `R` and translation `p`, and `h` have identity rotation
and translation `t`. For a frame-chain reading take `g = g_AB` and
`h = g_BC`. For the reversed-product comparison below, treat both as active
maps in one common coordinate frame; `g_BC g_AB` would not be a compatible
labelled chain.

Derive the expected values from the axis action: rotating `(x,y,z)` yields
`(-y,x,z)`, then shifting by `p` gives `(1-y,2+x,3+z)`. Translation by
`t` gives `(x+2,y,z)`. Substitution into these coordinate expressions,
independently of a Lean composition implementation, gives:

| Quantity | Exact expected value |
| --- | --- |
| `g(h(x,y,z))` | `(1-y,4+x,3+z)` |
| `h(g(x,y,z))` | `(3-y,2+x,3+z)` |
| Translation of `g * h` | `(1,4,3)` |
| Translation of `h * g` | `(3,2,3)` |
| `g * h` acting on point `(1,1,1)` | `(0,5,4)` |
| `h * g` acting on point `(1,1,1)` | `(2,3,4)` |
| `g` acting on point `(1,1,1)` | `(0,3,4)` |
| `g` acting on displacement `(1,1,1)` | `(-1,1,1)` |

Independently solve `X=1-y`, `Y=2+x`, `Z=3+z`: the inverse sends
`(X,Y,Z)` to `(Y-2,1-X,Z-3)`. Its rotation is `Rᵀ`, its translation
is `(-2,1,-3)`, and it sends `(0,3,4)` back to `(1,1,1)`. The inverse of
`g*h` sends `(X,Y,Z)` to `(Y-4,1-X,Z-3)`, in particular `(0,5,4)` back
to `(1,1,1)`. These values can detect a swapped composition order, an inverse
that only negates translation, and confusion between point and vector actions.
The derivation does not certify an implementation until its named Lean examples
have been checked.

## Rotation-exponential conventions

`Rotation.exp ω t` is Mathlib's actual matrix exponential of `t • Vec3.hat ω`,
packaged as `Rotation`. Any constant ω is allowed, including zero. For a unit
axis, t has the signed-angle/radian and unit angular-rate interpretation used
by MLS p27 eqs2.8-2.9; it does not mean that every point on the body has unit
linear speed. Rescaling satisfies `exp (c • ω) t = exp ω (t*c)`.

**Verified - formal statements:** the I3 build and audit
checks `Rotation.matrix_exp_mem` for arbitrary real skew matrices, including
determinant +1; `Rotation.hasDerivAt_exp_act` and `exp_zero_act` prove the actual
point trajectory has derivative `ω × q(t)` and the prescribed initial point.
This is a solution property, without a uniqueness or physical-calibration claim.
`Vec3.hat_sq` and `hat_cube` use Euclidean norm for every vector. The Rodrigues
theorem `exp_hat_of_norm_eq_one` requires unit norm, `exp_hat_of_ne_zero`
requires nonzero axis for its norm denominators, and `exp_hat_zero` gives the
identity separately.

The [checked exact examples](../../RoboLean/Examples/RotationExp.lean) equate
exp(+z,π/2) to the independently specified right-handed quarter turn, send e_x
to e_y, fix e_z, and equate exp(2e_z,π/4) to the same turn. Those examples check
conventions; the general representation results below have separate evidence.

## Rotation representations and selected coordinates

**Verified - formal statements:** the final build and audit
check [RotationSurjectivity](../../RoboLean/Geometry/RotationSurjectivity.lean),
including unit-axis representations of identity and half-turns.
The correctness theorem for the generic axial formula in
[RotationLog](../../RoboLean/Geometry/RotationLog.lean) requires
`sin(principalAngle R) ≠ 0`; endpoint cases have separate existence and
selection results. [RotationAxisUniqueness](../../RoboLean/Geometry/RotationAxisUniqueness.lean)
restricts signed-axis and angle uniqueness to `0<θ<π`. For the same half-turn,
unit axes agree up to sign, and distinct unit axes can represent identity.
[RotationParameters](../../RoboLean/Geometry/RotationParameters.lean) uses a
unit-axis premise for `2π` periodicity; simultaneous axis/parameter sign reversal
is also stated for arbitrary axes.

The Euler convention is `Rz(α) Ry(β) Rz(γ)`, with the right factor acting first
on column coordinates. [EulerAngles](../../RoboLean/Geometry/EulerAngles.lean)
uses `atan2(y,x)=arg(x+i y)` and proves its inverse for
`r=sqrt(R₂₀²+R₂₁²)>0`, giving the middle angle `0<β<π`.
At the singular middle-angle endpoints `β=0,π` (`r=0`) the angles `α=0`,
`γ=atan2(R₁₀, R₁₁)` with `β` the same `atan2` value reconstruct `R`
([SphericalWristAngles](../../RoboLean/Kinematics/SphericalWristAngles.lean)); this
is one member of the family of solutions there, and with the inverse for `r>0` it
makes the ZYZ map onto `SO(3)` with `0≤β≤π`. No global smooth or unique Euler chart
is supplied.
[ElementaryRotations](../../RoboLean/Geometry/ElementaryRotations.lean) separately
identifies all three displayed axis-rotation families with actual exponentials.
[UnitQuaternion](../../RoboLean/Geometry/UnitQuaternion.lean) covers the scalar-first
product and norm-one group, and [QuaternionRotation](../../RoboLean/Geometry/QuaternionRotation.lean)
the rotation map. **Quaternion rotation map.** The rotation of a quaternion `q = (q₀, q⃗)` is
`v ↦ q v q*` on pure quaternions `(0, v)`, with matrix `(q₀² - ‖q⃗‖²) I + 2 q⃗ q⃗ᵀ + 2 q₀ q̂⃗`
(`QuaternionCoordinates.rotationMatrix`), defined for every quaternion and in `SO(3)` for unit ones;
MLS p. 34 calls it "a detailed calculation". The axis-angle quaternion is
`(cos(θ/2), ω sin(θ/2))`; for a unit axis its rotation is `exp(ω̂θ)`. The map from unit quaternions
is a homomorphism onto `SO(3)` with kernel `{1, -1}`: a double cover, never a bijection, and
`θ ↦ θ + 2π` negates the quaternion. The extracted angle is `θ = 2 cos⁻¹ q₀ ∈ [0, 2π]` with Mathlib's
`Real.arccos`, so `sin(θ/2) = ‖q⃗‖`; the extracted axis is `q⃗ / sin(θ/2)`, zero at the endpoints
`q = ±1` (`θ = 0`, `2π`) by Lean's division, where every unit axis represents `q`; the printed guard
`θ ≠ 0` misses the endpoint `θ = 2π` (checked with commit `7117f86`).

[TwistSurjectivity](../../RoboLean/Geometry/TwistSurjectivity.lean) proves that
every proper rigid transform is an actual twist exponential, using pure
translation when the chosen rotation angle is zero.
[TwistLog](../../RoboLean/Geometry/TwistLog.lean) selects a global noncomputable
principal exponential coordinate whose exponential at parameter one reconstructs
the transform. Its positive-angle construction uses the actual inverse
translation coefficient on `0<θ<2π` and scales both twist components; zero
rotation is handled separately. This selection has no proved global smoothness
or uniqueness guarantee and is not a numerical logarithm implementation.

**Definition 2.1 and its converse (pp. 21–22).** A map `g : Vec3 → Vec3` is a rigid body
transformation (`IsRigidBodyTransformation`) when it preserves Euclidean distances and
`g(p + v × w) − g(p) = (g(p + v) − g(p)) × (g(p + w) − g(p))` at every base point `p`: the action on
vectors is defined by differences of points, as printed. The converse needs only the base point
`0`: such a map is affine (Mathlib's `Isometry.affineIsometryOfStrictConvexSpace`, which needs no
surjectivity), its linear part is orthogonal, and the cross-product clause forces determinant `+1`;
so the maps of Definition 2.1 are exactly the point actions of `SE(3)`, and the reflection of p. 21
is excluded. A raw `Fin 3 → ℝ` sup norm would make the length clause a different claim.

**The plane and `SE(2)` (Exercises 10–11, pp. 75–76).** Planar points and vectors are
`Vec2 := EuclideanSpace ℝ (Fin 2)`, ordered `(x, y)`; the planar grasp modules keep `Fin 2 → ℝ` for
their positions. `PlanarRotation` is Mathlib's `specialOrthogonalGroup (Fin 2) ℝ`; `ofAngle θ` is
`[[cos θ, −sin θ], [sin θ, cos θ]]`, counterclockwise for `θ > 0`; `ω̂ = [[0, −ω], [ω, 0]]`. A planar
rigid motion `(p, R)` has named fields `rotation`, `translation`, composes as `RigidTransform` does
(`g * h` applies `h` first), and has the homogeneous matrix `[[R, p], [0, 1]]` with coordinates
`x, y`, homogeneous. A planar twist is `(v, ω)` with hat `[[ω̂, v], [0, 0]]`. The embedding into
`SE(3)` sends `(p, R)` to `((p, 0), [[R, 0], [0, 1]])`, a rotation about `+z` followed by a
translation in `z = 0`, and is a group homomorphism. The unit circle is `Metric.sphere 0 1` in
`Vec2`, matched with `SO(2)` by the first column. Planar velocities (Exercise 11(d)) take the
derivative of the homogeneous matrix entry by entry; `ġg⁻¹` and `g⁻¹ġ` use the inverse in `SE(2)`.

**Cayley parameters (Exercise 5, p. 73).** `R_a = (I − â)⁻¹(I + â)` with `â = Vec3.hat a` and
Mathlib's matrix inverse; `det(I − â) = 1 + ‖a‖²`, so the inverse always exists. The recovery
`â = (R − I)(R + I)⁻¹` needs `R + I` invertible, a hypothesis the exercise does not print: every
`R_a + I` is invertible, so the rotations by `π` have no Cayley parameters.

**Eigenvalues and projections (Exercises 3 and 9, pp. 73, 75).** Characteristic polynomials are
Mathlib's `Matrix.charpoly`, `det(XI − A)`, over `ℝ`; the complex roots are given by the
factorizations `(z − i)(z + i) = z² + 1` and `(z − e^{iθ})(z − e^{−iθ}) = z² − 2 cos θ z + 1` over
`ℂ`, and the complex eigenvectors of `ω̂` in their real form (the quarter turn `u ↦ ω × u` on
`ω^⊥`). `N_ω` is the set of multiples of `ω` and `N_ω^⊥` the vectors with `⟨ω, u⟩ = 0`, in `Vec3`; a
projection map onto `V` is a linear map with image `V` fixing `V`, as printed.

**The remarks of p. 33.** Euler angles are singular as in Exercise 3.14 (p. 150): as the three-joint
chain of their axes, with a singular Jacobian; ZYX angles are singular exactly at `cos θ = 0`, both
`θ = ±π/2` (the printed `−π/2` names one). "Singularities can never be eliminated in any
3-dimensional representation of `SO(3)`" is read as the nonexistence of a global chart, a
homeomorphism from `SO(3)` (subspace topology of `3 × 3` matrices) onto an open subset of `ℝ³`;
the smooth-map form is not formalized.

**Quaternion rates and degrees of freedom (Exercises 6(e) and 7, p. 74).** The body rotating at unit
velocity about a unit `ω` from the identity is represented by `Q(t) = (cos(t/2), ω sin(t/2))`, the
derivative taken in Mathlib's `Quaternion ℝ`. The degrees of freedom of a rigid body in `ℝⁿ` are read
as the dimension of the rigid velocities `ℝⁿ × so(n)`, `so(n)` the skew-symmetric matrices
(Mathlib's `LieAlgebra.Orthogonal.so`).

**Example 2.1 and Figure 2.17.** Example 2.1's `g_ab(θ) = (R_z(θ), (0, l₁, 0))` takes `B`- to
`A`-coordinates. Figure 2.17 is read with both joints about vertical axes, `C₁` at height `l₀` on
the first axis, `C₂` at `l₁` along `x` with no vertical offset (none is dimensioned) and `C₃` at
`l₂` along `x`, all frames aligned in the reference configuration; its velocities are the library's
spatial and body velocities of the pose curve along differentiable joint trajectories, from the
product of exponentials `e^{ξ̂₁θ₁}e^{ξ̂₂θ₂}g(0)`.

## Twist, adjoint, and wrench conventions

Use twist order `(v, ω)` and wrench order `(f, τ)`, with linear coordinates
first. Twists are a two-field structure `Twist` with fields `linear` and `angular`,
the twist coordinates `(v, ω)` of MLS printed p. 41, eq. (2.30), with the componentwise
real vector-space structure; a `Vec3 × Vec3` value is rejected where a twist is expected
(commit `a92475e`). Wrenches are a distinct two-field
structure `Wrench` with fields `force` and `torque` on the same pattern, so a twist is
rejected where a wrench is expected and conversely
(commit `d33f59e`). The two carriers
are related only through named maps: the power pairing `Wrench.pair`, the coordinate swaps
`Twist.swapWrench` and `Wrench.toTwist`, and the dual equivalences `Wrench.pairingEquiv`
and `Twist.pairingEquiv`. Neither carrier has a norm, metric or topology; a six-coordinate
norm, if one is ever needed, must be chosen with its metric and length scale and declared
deliberately. The separation is between the typed values `Twist` and `Wrench`, not between their literals: an anonymous constructor `⟨a, b⟩` elaborates as whichever of the two the slot expects, so the component order inside a literal is a convention the types do not check (an observation of 2026-10-10). The [ledger](mls-coverage-ledger.md)
distinguishes the checked algebra and derivative statements below from remaining
and partial source obligations. For a differentiable pose trajectory `g(t)`,

\[
\widehat\xi=\begin{bmatrix}\widehat\omega&v\\0&0\end{bmatrix},\qquad
\widehat V^{s}=\dot g g^{-1},\qquad
\widehat V^{b}=g^{-1}\dot g,\qquad
V^s=\operatorname{Ad}_g V^b,
\]

\[
\operatorname{Ad}_{(p,R)}=
\begin{bmatrix}R&\widehat p R\\0&R\end{bmatrix}.
\]

Sources: p.41, equations (2.30)-(2.31),
pp.54-55, equations (2.53), (2.55), (2.57)-(2.58).
In particular `vˢ = ṗ - ωˢ × p`; it is generally not the velocity `ṗ` of the
body origin. Body linear velocity is `vᵇ = Rᵀ ṗ`.

Wrench torque is about the origin of its stated frame. For the equivalent
wrench transferred from B's origin to A's origin and expressed in A,

\[
F_A=\operatorname{Ad}_{g_{AB}^{-1}}^{\mathsf T}F_B,\qquad
f_A=R_{AB}f_B,\qquad
\tau_A=p_{AB}\times(R_{AB}f_B)+R_{AB}\tau_B.
\]

This includes an origin shift, not merely rotation of components. Equivalently
`Fᵇ = Ad_gᵀ Fˢ`. Source:
pp.61-63, equations (2.65)-(2.67).
The dual pairing is `f·v + τ·ω`; with velocity units it is instantaneous power,
whose time integral is work. MLS denotes the pairing by `δW`; RoboLean's
`Wrench.pair` states the instantaneous pairing. I4 proves preservation under
compatible `Wrench.transform` and `Twist.adjoint` transformations. The later
interval-work theorems below retain actual derivative and integrability premises.

### Checked subset and assumptions

**Verified - formal statements:** the I4 build and audit
check the [Twist](../../RoboLean/Geometry/Twist.lean) hat/vee linear equivalence
with the independent `se(3)` matrix carrier and
[TwistAdjoint](../../RoboLean/Geometry/TwistAdjoint.lean)'s coordinate matrix,
conjugation, inverse, and representation laws. [TwistExpAdjoint](../../RoboLean/Geometry/TwistExpAdjoint.lean)
proves conjugation identities for the actual matrix exponential.

`Twist.exp ξ θ` packages the actual homogeneous matrix exponential. The
[closed-form theorems](../../RoboLean/Geometry/TwistExpClosedForm.lean) give
rotation `I` and translation `θv` when `ω=0`, and
`(I-R)(ω×v) + θω(ω·v)` when `‖ω‖=1`, with `R=exp(θhat(ω))`.
The unit premise comes from the derivation on MLS p41 even though the box on
p42 only prints `ω≠0`. For arbitrary nonzero `ω`, normalization divides
both `v` and `ω` by `a=‖ω‖` and changes the parameter to `aθ`.
The all-zero twist and the zero-angular branch remain explicit.
[TwistExpJacobian](../../RoboLean/Geometry/TwistExpJacobian.lean) proves the
translation coefficient has determinant `2θ(1-cos θ)` and is invertible for
unit `ω` and `0<θ<2π`; it also proves determinant zero at `θ=2π`.
This coefficient theorem is separate from the later existence and selected-coordinate
results above; it does not assert a unique global logarithm.

[TwistTrajectory](../../RoboLean/Geometry/TwistTrajectory.lean) proves the
actual constant-twist point ODE and initial value, including left action on
an initial pose. [RotationVelocity](../../RoboLean/Geometry/RotationVelocity.lean)
and [RigidVelocity](../../RoboLean/Geometry/RigidVelocity.lean) require actual
`HasDerivAt` hypotheses for the rotation or homogeneous trajectory. They derive
skew angular-velocity matrices, the displayed spatial/body coordinates, point velocity,
and the adjoint relation. [RigidVelocityComposition](../../RoboLean/Geometry/RigidVelocityComposition.lean)
checks product, fixed-frame, and inverse velocity laws under those derivative
premises. For `g(t)=Twist.exp ξ (θ(t)) * g₀`,
`RigidTransform.spatialVelocity_exp_mul` and `bodyVelocity_exp_mul` give
`Vˢ=θ̇ξ` and `Vᵇ=θ̇ Ad_(g₀⁻¹)ξ`, with fixed `ξ,g₀` and an actual scalar
derivative for `θ`. These are solution and coordinate identities, without an
ODE uniqueness or physical-calibration claim.

[Wrench](../../RoboLean/Geometry/Wrench.lean) identifies its independently
written coordinate transformation with the literal transpose of the inverse
adjoint matrix, proves `Wrench.pair_transform_adjoint`, and transforms finite
wrench sums to a common frame before summing. `Wrench.Equivalent` quantifies
over every instantaneous twist; `equivalent_iff_eq` identifies this algebraic
notion with coordinate equality. Neither the pairing nor these equivalence
laws alone establish contact feasibility, actuator limits, or an energy balance.
Exact [twist](../../RoboLean/Examples/Twist.lean), [wrench](../../RoboLean/Examples/Wrench.lean),
and [velocity](../../RoboLean/Examples/Velocity.lean) examples check selected
conventions. [PlanarVelocity](../../RoboLean/Examples/PlanarVelocity.lean) supplies
parameterized mechanism derivative examples; general joint/chain kinematics
remains separate, as recorded in the ledger.

### Geometric screws, brackets, and work

The final formal check of commit `b2d79fe`
and its source review
bind these additional statements to their exact assumptions.
[TwistScrewMotion](../../RoboLean/Geometry/TwistScrewMotion.lean) defines geometric
finite-pitch, pure-translation, and stationary data independently of the twist
exponential. Finite and translation directions are unit vectors, while the
motion parameter is any signed real. Its agreement theorem proves the actual
point action `R(x-q)+q+hθω`, including zero parameter, and axis points move by
`hθω`. Axis-point shifts leave the motion unchanged.
[Chasles](../../RoboLean/Geometry/Chasles.lean) proves existence of this geometric
description for every proper rigid displacement, without axis uniqueness at
identity or pure translation and without a trajectory-equivalence claim.

[ScrewAxis](../../RoboLean/Geometry/ScrewAxis.lean) uses actual affine lines;
finite-axis, pure-translation, and zero cases remain distinct.
[NormalizedTwist](../../RoboLean/Geometry/NormalizedTwist.lean) normalizes nonzero twists by scaling
both components, and a norm-based magnitude scales by the absolute scalar.
[ScrewConjugation](../../RoboLean/Geometry/ScrewConjugation.lean) transforms an
axis point by `g.applyPoint` and its directed vector by `g.applyVector`, keeping
pitch and signed parameter. This geometric change agrees with `g H g⁻¹` for
the actual displacement. Reversing the directed axis and parameter together
preserves motion; reversing the axis alone is not asserted to do so.
The absolute-pose fixed-line formula requires `cos θ ≠ 1`, excluding every
full turn; the relative-motion formula includes zero angle.

[TwistBracket](../../RoboLean/Geometry/TwistBracket.lean) and
[AdjointBracket](../../RoboLean/Geometry/AdjointBracket.lean) establish coordinate
Lie-bracket, matrix-commutator, and adjoint compatibility statements. The selected
Appendix A inventory
records L01–L04; these coordinate results do not supply a global tangent or
manifold interface.

[WrenchWork](../../RoboLean/Geometry/WrenchWork.lean)'s `intervalWork` is an
actual oriented interval integral of the pairing and requires
`IntervalIntegrable`. Its point-force work comparison uses a fixed body point
and supplied actual homogeneous-trajectory derivative data; integrated pose
results retain the stated derivative-family and integrability hypotheses.
Spatial/body work equality and additive work are mathematical integral identities,
without an energy-balance, feasibility, calibration, or numerical-quadrature claim.
[WrenchReciprocityGeometry](../../RoboLean/Geometry/WrenchReciprocityGeometry.lean)
uses geometric finite/infinite screw cases with actual affine axes. Its
angle/distance formula requires an explicit common-normal certificate, including
positive separation, nonparallel unit directions, and signed sine/cosine equations.
[ScrewCommonNormal](../../RoboLean/Geometry/ScrewCommonNormal.lean) constructs the certificate's data.
**Common normal and signed angle.** For nonparallel unit axes `l₁ = {q₁ + λω₁}`, `l₂ = {q₂ + λω₂}`
with `m = (q₂ - q₁)·(ω₁ × ω₂)`, the distance is `d = |m| / ‖ω₁ × ω₂‖` (the least distance between
the axes, attained by feet joined by `d n`), the normal is `n = ±(ω₁ × ω₂)/‖ω₁ × ω₂‖` with the sign
of `m` (so that `q₂ - q₁` has component `d ≥ 0` along `n`, the book's `q₂ = q₁ + d n` at the feet),
taken `+` when `m = 0`, and the angle is `α = atan2(n·(ω₁ × ω₂), ω₁·ω₂)` with the library's
`atan2`, so `cos α = ω₁·ω₂` and `sin α = ±‖ω₁ × ω₂‖`. The reciprocal product (2.72) with these data
equals the twist–wrench pairing for every pair of nonparallel finite screws, intersecting axes
(`d = 0`) included, where the sign of `n` does not matter. Parallel axes use `α = atan2(0, ω₁·ω₂)`
(`0` or `π`), for which the product does not depend on the distance. Infinite-pitch screws have no
form of (2.72); their reciprocity is stated directly (checked with commit `7117f86`).

**Hybrid velocity (Exercise 18, pp. 78–79).** `V^h = (ṗ, ωˢ)` is read from the derivative of the
homogeneous pose matrix, with the same derivative evidence as `spatialVelocity`; linear coordinates
come first. `Ad_p` and `Ad_R` in part (b) are the adjoints (2.58) of the pure translation `(p, I)` and
the pure rotation `(0, R)`. A fixed change of spatial frame multiplies the pose on the left, a fixed
change of body frame on the right. A body wrench in hybrid coordinates is
`F^h = Wrench.transform (0, R) Fᵇ = (R fᵇ, R τᵇ)`: the same force and moment at the body origin,
written in the orientation of the spatial frame; under a change of body frame the body wrench is
re-expressed at the new body origin by `Wrench.transform b⁻¹`.

## Source inspection and evidence scope

**Verified - source transcription only:** rendered inspection of printed
pp.23, 25, 26, 31, 35-38, 41-42, 54-55, and 61-63 of
MLS.pdf supports the displayed coordinate-direction,
sign, ordering, composition, inverse, homogeneous, adjoint, and wrench formulas.
Printed p.24 and the surrounding pp.23-38 and 53-56 passages were also extracted
as text. This is not a review of every argument in Chapter 2.

Extraction used `pdftotext -f 41 -l 56 -layout references/MLS.pdf -` and
`pdftotext -f 71 -l 74 -layout references/MLS.pdf -`. Twist/wrench extraction
also used PDF pp.57-82; its displayed output was truncated, so the claims above
use the individually inspected rendered formula pages. Rendering used
`pdftoppm -f N -l N -r 110 -png -singlefile references/MLS.pdf /tmp/robo-conventions-pdfs/mls-pdf-N`,
for `N` equal to `41, 43, 44, 49, 53, 54, 55, 56, 59, 60, 72, 73, 79, 80, 81`.
These commands exited zero; the named PNGs were opened and visually inspected.
The temporary renderings are inspection aids, not durable library artifacts.

**Verified — additional source transcription, 2026-10-09:** at I2,
printed pp.26–28 and 37–38 were re-rendered and opened to compare cross-product, hat,
skew-space, conjugation, and vector-action formulas with the named declarations.
The source-inspection record and preserved
renderings bound that review.

**Verified - additional bounded source inspection, I3:** rendered printed
pp27-31 and every page pp39-69 were opened, preserved with the
source review and
P2 inventory.
The I4 normalization now proves rescaling of the full twist `(v,ω)`.
The later screw APIs distinguish zero, finite pitch, and pure translation;
parameters remain signed while norm-based magnitude scales by abs(θ).
Reciprocal-system power and dimension statements do not establish physical
contact feasibility.

**Verified - additional bounded source inspection, I4:** the
source-statement review maps the new declarations
to MLS printed pp39–44 and 51–64 and records the unit-axis premise, full-twist normalization,
full-turn exclusion, derivative hypotheses, and instantaneous-power scope.
The [ledger](mls-coverage-ledger.md#implementation-evidence-i4) distinguishes
these checked statements from partial and remaining source obligations.

The final source-statement review
records the subsequent rotation, logarithm, Euler, bracket, screw, and work scope,
including the named domain restrictions and remaining partial obligations.

**Unverified here:** numerical refinement, physical interpretation of a particular
robot, and user acceptance. Named formal-statement evidence is cited above and
in the coverage ledger; this document does not establish full implementation
conformance with the book.

## Kinematics conventions

Recorded 2026-10-09 UTC with commit `3e5bdd1`.
Source: MLS Chapter 3, printed pp. 83–89, 95 and 115–118, extracted as text and,
for pp. 87, 88 and 116–118, inspected as rendered images in this increment. These
are coordinate conventions of the Lean model; they do not certify a physical robot.

**Joint and link numbering.** Joints are numbered from the base to the tip
(p. 83). Lean indexes joints by `i : Fin n`,
so Lean joint `i` is the book's joint `i + 1`. Links are indexed by `Fin (n + 1)`;
link 0 is the base, and Lean joint `i` connects link `i` (`Fin.castSucc i`) to
link `i + 1` (`Fin.succ i`), as in "joint i connects links i − 1 and i".

**Joint coordinates and admissible domain.** Joint coordinates are real numbers,
`θ : Fin n → ℝ`. The book's revolute coordinate lives on `S¹`, with `2π`
identified with `0` (p. 84); Lean keeps the
real lift and proves periodicity instead of forming a quotient
(`SerialChain.fk_add_int_mul_two_pi`, for revolute joints with a unit axis). A
real vector therefore names a configuration, but two vectors that differ by `2π`
multiples in revolute coordinates give the same pose; no torus type is defined.
The admissible set `Q` of p. 84 is an explicit `Set (Fin n → ℝ)`: the chain field `SerialChain.admissible` (default: all of `Fin n → ℝ`), and an explicit argument `Q` of every workspace definition. The field is read by the variants `admissibleCompleteWorkspace`, `admissibleReachableWorkspace`, `admissibleDextrousWorkspace` and `admissibleAlternativeDextrousWorkspace`, which fix `Q := c.admissible`, and by the closed-chain joint space `ClosedChain.admissible`; the forward kinematics and the `Q`-parametrized definitions do not read it (commit `c2a2604`, which gave the field a use rather than removing it). MLS p. 84 measures angles with a
right-handed convention ("clockwise as viewed along the direction of the axis",
which is the right-hand rule seen with the axis pointing away from the viewer);
it agrees with the positive quarter turn about `+z` above.

**Reference configuration and twists.** The reference configuration is `θ = 0`,
and `SerialChain.toolRef` is `g_st(0)`. Reference joint twists are base-frame
twists at `θ = 0` (p. 87), in the order
`(v, ω)`: revolute `Twist.revolute ω q = (-ω × q, ω)` and prismatic
`Twist.prismatic v = (v, 0)` (in Lean, `⟨-ω × q, ω⟩` and `⟨v, 0⟩`). The unit-axis or unit-direction premise is the
predicate `Twist.IsRevoluteJoint` or `Twist.IsPrismaticJoint`, not a field of the
chain; the chain accepts any twist, and theorems state the joint type they need.
Any point of the axis line gives the same revolute twist
(`Twist.revolute_axis_point`).

**Forward kinematics.** `SerialChain.fk c θ = exp(ξ₁θ₁) ⋯ exp(ξₙθₙ) g_st(0)`
(eq. (3.3)) is the ordered product `List.prod (List.ofFn …)`, base joint on the
left. Since `g * h` applies `h` first, the tip joint's motion acts first on the
reference tool pose, and the result acts on `g_st(0)` by left multiplication, as
in `g_ab(θ) = exp(ξ̂θ) g_ab(0)` (p. 85).
The adjacent-frame form (eq. (3.1)) is `LinkFrameChain`: the joint twist `ζᵢ` is
written in the proximal link frame `Lᵢ` (`L₀ = S`), the relative transform is
`g_{Lᵢ Lᵢ₊₁}(θᵢ) = exp(ζ̂ᵢθᵢ) g_{Lᵢ Lᵢ₊₁}(0)`, and the base-frame twist is
`ξᵢ = Ad_{g_{S Lᵢ}(0)} ζᵢ`.

**Sequential joint motion.** `SerialChain.moveJoint` holds every link state as an
active rigid displacement from the reference configuration, in base coordinates.
Moving joint `i` by `t` leaves links `0..i` in place and left-multiplies every
distal link by `exp(Ad_{G i} ξᵢ, t)`, the screw motion about the joint axis as
currently carried by its proximal link (pp. 86–87). The tool pose of a state is
`G n * g_st(0)`.

**Jacobians.** A Jacobian is the function `Fin n → Twist` of its columns, and
joint rates act by `∑ i, θ̇ i • J i`. Lean column `i` is the book's column
`i + 1`. Spatial column `i` is `Ad` of the product of the first `i` joint
exponentials applied to `ξᵢ` (eq. (3.54), p. 116);
body column `i` is `Ad` of the inverse of (joint exponentials `i..n−1`) `g_st(0)`
applied to `ξᵢ` (eq. (3.55), p. 117).
The `6 × n` matrix view `SerialChain.spatialJacobianMatrix` has rows indexed by
`Fin 3 ⊕ Fin 3` through `Twist.coordinates`: `Sum.inl` rows are `v_x, v_y, v_z`,
`Sum.inr` rows are `ω_x, ω_y, ω_z`, the row order printed on p. 118. The spatial
velocity of the forward-kinematics curve is `RigidTransform.spatialVelocity`,
computed from an actual `HasDerivAt` derivative of the homogeneous pose; the
tool-origin velocity is `ωˢ × p + vˢ`, not `vˢ` alone (p. 117).

**Workspaces.** `completeWorkspace c Q` is the pose image `fk '' Q` (eq. (3.11)),
`reachableWorkspace c Q` the position image (eq. (3.12)), and
`dextrousWorkspace c Q` is `{p | ∀ R, ∃ θ ∈ Q, fk θ = ⟨R, p⟩}` with the printed
quantifier order (eq. (3.13), p. 95), `R`
ranging over all of `SO(3)`. These are pose-reachability sets; they say nothing
about paths, continuity of an inverse, or dynamics.

**Force pullback.** Joint torques equivalent to an end-effector wrench are the pairings
`τᵢ = Wrench.pair F Jᵢ` of the wrench with the Jacobian columns, in matched frames: a
spatial wrench (moment about the base origin, base coordinates) with the spatial Jacobian,
`SerialChain.spatialWrenchTorques` (eq. (3.60), p. 121),
and a body wrench (moment about the tool origin, tool coordinates) with the body Jacobian,
`SerialChain.bodyWrenchTorques` (eq. (3.59)). The two correspond by
`Fˢ = Wrench.transform (fk θ) Fᵇ`, the inverse of `Fᵇ = Ad_gᵀ Fˢ` (eq. (2.67),
p. 63). The matrix forms use `spatialJacobianMatrix` and
`bodyJacobianMatrix` with rows `Sum.inl` = `v`, `Sum.inr` = `ω`, against `Wrench.coordinates`
with `Sum.inl` = `f`, `Sum.inr` = `τ`. The statements are the instantaneous algebraic
identity; the book's frictionless work premise is not formalized
(commit `f237457`).

**Planar two-link workspace.** The motion plane of `Examples.planarTwoLink` is the third
coordinate zero, `x 2 = 0` (joint axes `+z`, zero configuration along `+y`), and distances
are the Euclidean norm of `Vec3`. "Unrestricted joints" is `Q = Set.univ`. The annulus,
certificate and radial-band statements are design statements from the assessment, not MLS
results ([ledger C01–C07](mls-coverage-ledger.md#design-certificates-beyond-mls)).

**Planar two-link inverse kinematics.** MLS p. 98, eq. (3.16), is stated about the library arm
`planarTwoLinkPosition a b`. The book's Fig. 3.7a puts the zero configuration along `+x`, the
library's arm (Example 3.1 specialized) along `+y`; the book's point `(x, y)` is the library point
`vec (−y) x 0`, a rotation by `Rz(π/2)` (`Examples.planarTwoLinkPosition_eq_vec_iff`), with
`l₁ = a`, `l₂ = b`, `θ₁ = q 0`, `θ₂ = q 1`. `α = planarTwoLinkAlpha a b r` and
`β = planarTwoLinkBeta a b r` are the printed `cos⁻¹` expressions with `Real.arccos` (total:
`π` below `−1`, `0` above `1`), so every statement that uses them carries the annulus bounds that
put the arguments in `[−1, 1]`; `atan2` is `Rotation.atan2`. Positive lengths and `r ≠ 0` are
explicit hypotheses the book does not state; the branches are paired as printed (`+α` with `+β`,
`−α` with `−β`) and solutions are modulo `2π` in each angle. The workspace row C02's elbow angle
`arccos((r² − a² − b²)/(2ab))` is the `π − α` branch.

**Supervisor models and the Veil correspondence.** A supervisor model in `RoboLean/Design/` (commit `9c8b539`, 2026-10-10) is a
transition system over an abstract target type: a `State` structure, an `init` state, an
inductive `Step` relation with one constructor per action and the action's `require` clauses as
hypotheses, and reachable states `Relation.ReflTransGen Step init`. It mirrors a Veil model in
the sibling project `robo-lean-veil` declaration by declaration: a Veil relation
`r : target → Bool` is a Lean `Set Target` with `t ∈ s.r` read as `r t = true`; a Veil
`individual b : Bool` is a `Bool` field; Veil's immutable (theory) relation `reachable` is the
Lean predicate parameter `reachable : Target → Prop` of `Step`; `after_init` is `init`; a
`safety` clause is a `Prop`-valued predicate on states; the verification conditions
`<action>_<clause>` are the cases of the step-preservation theorem, and Veil's `doesNotThrow`
conditions have no counterpart because a Lean step cannot fail. For the planar two-link arm the
guard is `planarGuard a b`, C04's condition verbatim. The two projects run on different Lean
versions and cannot import each other, so the correspondence is a recorded convention, checked
only by reading the two files side by side (the table in commit `9c8b539`), not by any kernel. The finite
instance of a Veil model may carry a guard table computed from concrete targets; the first pilot's table is
`planarGuard 2 1` at five tool positions, checked on the Lean side. Veil action names must avoid
the fields `distinct` and `complete` of Veil's generated action-tag class. A Veil `individual x : Nat` is a Lean `ℕ` field, and an immutable (theory) `individual bound : Nat`
is a Lean parameter `bound : ℕ` of `Step`, like the guard (commit `7e752fe`). A supervisor that extends another one extends
its `State` structure (`structure State extends PlanarArmSupervisor.State`), and its relation to
the smaller supervisor is a simulation theorem (`ReachableState.toState`: forgetting the new fields
maps each step to a step of the smaller supervisor or to no step), through which the smaller
supervisor's refinement theorems are reused rather than reproved. The SMT backend embeds Veil's
`Nat` into integers with nonnegativity assumptions (lean-smt's `Embedding/Nat` rewrites), so a
verification condition over `Nat` reaches cvc5 as linear integer arithmetic. A Lean theorem in a
Veil file about Veil's generated declarations passes the instance arguments exactly as Veil's
assembled transition system does (read with `pp.explicit`); left to instance synthesis, the first
application timed out at `whnf` in the second pilot (commit `7e752fe`).
A Veil `function f : target → Nat` is a Lean field `f : Target → ℕ`, and its update
`f t := e` is `Function.update f t e`, which needs `[DecidableEq Target]` (Veil's generated
theorems carry `DecidableEq target` too); `Nat` subtraction truncates on both sides. An immutable
individual that only `after_init` reads (`capacity`, read by `budget := capacity`) is a parameter of
`init` rather than of `Step` (commit `bd7b9e8`).
A supervisor that extends a supervisor which itself extends another names its parent projection
(`structure State extends toTimeoutState : PlanarArmTimeoutSupervisor.State Target`), because the
default name `toState` collides with the inner parent projection; its simulation then maps each
step to the step of the same name when the new guards only strengthen existing actions. lean-smt
embeds a `Nat`-valued function as an `Int`-valued one with the assertion `∀ a₁, f a₁ ≥ 0`, and
rewrites `x - y` into `if x ≥ y then x - y else 0`; with such a function in a model, debug with
`trace.smt` (goal and query), not `trace.smt.solve`, whose proof printer fails on the binder `a₁`
(commit `bd7b9e8`).
A Veil model's `/` and `%` on `Nat` are Lean's `Nat.div` and `Nat.mod` (the actions are Lean code),
with `n / 0 = 0` and `n % 0 = n`, and the Lean mirror uses the same operations; lean-smt sends them
to cvc5 as integer `div` and `mod` (embedding lemmas `Int.natCast_ediv`, `Int.natCast_emod`), where
division by zero is unspecified, so a Veil model states a positive divisor as an `assumption` on the
theory (`assumption [period_pos] period ≥ 1`), which every condition carries as its `Assumptions`
premise and Veil's `reachable.init` requires, while the Lean mirror takes `1 ≤ period` only where
Lean's conventions need it (commit `aa74623`). With `veil.smt.trust false`, a condition whose refutation involves `div` or `mod`
does not reconstruct at this Veil and lean-smt revision; such conditions are discharged by a solver
fallback set in the model (`set_option veil.solver "custom"` with a `macro_rules` for `veil_solve`
that tries `veil_smt` first, then `grind`, core lemmas and hand-proved steps), which leaves every
condition that SMT reconstruction discharges unchanged (commit `aa74623`). A product clause is mirrored
literally (`bound * closedCount`, `age * age`, `rate * ticksTotal`); an auxiliary equality such as
`load = age * age` is a clause of its own on both sides.
A counter that wraps around at a theory constant is encoded without `div` and `mod`: `if slot + 1 =
period then slot := 0; rounds := rounds + 1 else slot := slot + 1` in the Veil action, the clauses
`slot < period` and `period * rounds + slot = ticksTotal`, and in the Lean mirror the same `if` in
the two updated fields; `ticksTotal % period = slot` and `ticksTotal / period = rounds` are then
Lean theorems derived from the two clauses for `1 ≤ period`, not Veil clauses. With `veil.smt.trust
false` this encoding needs no solver fallback at this Veil and lean-smt revision (every
per-condition proof reconstructs), and on states with `slot < period` its step relation equals the
`div`/`mod` one (commit `44a91b2`), so it
is the preferred form; the fallback chain of commit `aa74623` remains the route for a model that must keep `div` or
`mod`. A bounded exclusion is recorded as a theorem only in Veil's proof-term form `unsat trace [n] {
… } by veil_bmc`, followed by `#print axioms n`: Veil's ordinary `unsat trace` keeps no proof term and
reports an `unsat` solver result as holding even when the proof was not rebuilt or would fail the
kernel (commit `44a91b2`: silent over four actions, rejected by the kernel in the proof-term form).

**Arrival times of the planar arm demo.** The arrival statements concern the ideal continuous
model: from the time `t₀ ≥ 0` at which a target `(x, y)` is commanded the arm is held at the fixed
set point `θ_d = elbowDown a b x y` (`Demo.setPoint`), the closed loop is any field with an
exponential bound `ExponentialBoundOn f (θ_d, 0) C α ρ` (a hypothesis structure, discharged for the
demo's PD loop), and the initial state error `‖(θ(t₀) − θ_d, θ̇(t₀))‖ < ρ` is a hypothesis. The
position error is the Euclidean distance of the plane (`Examples.planarDist`, the demo's `hypot`)
between `planarArmXY a b θ(t)` in the book's frame and the target, bounded through the Lipschitz
constant `a + 2b` of `planarArmXY` from the sup norm, so a tolerance `ε` on the position is the
tolerance `ε/(a + 2b)` on the state. Samples are the times `t₀ + kh`; the design statement uses the
sample `t₀ + bound · h`, at which the demo loop's tick brings the age to the bound and after which
the loop would time the command out at the next sample; that timing is the loop's policy, not a
theorem. The demo arm's explicit constants (`C = 34`, `α(ρ) = 1/(24(256 + (2 + 34ρ)²))`) use the
moments `1/12` and `1/48` about the joint axes and leave the other principal moments free (checked
with commit `5a650af`).

**Inverse kinematics subproblems.** A zero-pitch unit twist (MLS
p. 99) is `Twist.revolute ω r` with the hypothesis
`‖ω‖ = 1`, where `r` is a point on the axis; `e^{ξ̂θ} p` is
`(Twist.exp ξ θ).applyPoint p`. With `u = p − r` and `v = q − r`, `PadenKahan.perp ω u` is
`u′ = u − ω ωᵀu` and `PadenKahan.planeAngle ω u v` is
`θ₀ = atan2(ωᵀ(u′ × v′), u′ᵀv′)` (eq. (3.28)), with the library's `Rotation.atan2`
(argument of `x + i y`, in `(−π, π]`, `atan2 0 0 = 0`). Angles are real numbers and
solutions are stated modulo `2π`. Subproblem 2 models intersecting axes by one axis point
`r` for both twists and treats the non-parallel case `ω₁ × ω₂ ≠ 0`; its zero, one or two
solutions are counted as intermediate points `c = e^{ξ̂₂θ₂} p` (eq. (3.21)). Subproblem 3
takes `δ ≥ 0` and the nondegeneracy `u′ ≠ 0`, `v′ ≠ 0`, which the book does not state
(commit `fc99877`). MLS
p. 98, eq. (3.16), prints the closed-form planar two-link
inverse kinematics; the existence half of the workspace row C02 is its `π − α` branch. The polar-form lemmas of `Rotation.atan2` are `Rotation.sqrt_mul_cos_atan2` and `Rotation.sqrt_mul_sin_atan2` in `Geometry/EulerAngles.lean`; the axis-fixing fact of MLS p. 104 is `Twist.exp_revolute_applyPoint_of_mem_axisLine` (commit `c2a2604`).

**Elbow manipulator.** MLS Example 3.2 (pp. 89–91) is `Examples.elbowManipulator l₀ l₁ l₂`, the base
frame with the first axis along `+z` and the arm along `+y` at height `l₀`; the twists are built
with `Twist.revolute` from the axes and points of Fig. 3.4 and agree with the six printed
six-vectors; `g_st(0) = (I, (0, l₁ + l₂, l₀))`. Example 3.5's points are the wrist centre
`p_w = (0, l₁ + l₂, l₀)` and the shoulder point `p_b = (0, 0, l₀)`; `g₁ = g_d g_st(0)⁻¹`
(eq. (3.30), `SerialChain.fk_eq_iff_poe_eq`) and `e^{−ξ̂θ}` is `Twist.exp ξ (−θ)`. Each step is
stated in the form of the corresponding `PadenKahan` subproblem, so its solution theorems apply
directly. The necessary conditions hold for every point of the sixth axis (Step 3) and every point (Step 4); the converse uses a point `p ≠ p_w` of the sixth axis and a point `p′` off it, the points the book prescribes, and characterizes all solutions. The eight-solution count reads the solutions modulo `2π` in `Fin 6 → Real.Angle`. The candidates
are indexed by `(b₁, b₂, b₃) : Bool × Bool × Bool`: `θ₃ = θ₀ + cos⁻¹ κ` for `b₁` true and
`θ₀ - cos⁻¹ κ` otherwise, the intermediate points of Steps 2 and 3 for `γ = √Γ` when `b₂`, `b₃` are
true and `-√Γ` otherwise, the other angles by the `atan2` formula of Subproblem 1, Step 3 at the point
`p_w + e_y` of the sixth axis and Step 4 at the point `p_w + e_x` off it. The count needs `l₁, l₂ ≠ 0`,
shoulder regularity (the wrist-centre target off the first axis) and wrist regularity (for each arm
branch, `g₂ (p_w + e_y)` off the fourth axis); exactly eight also needs `-1 < κ < 1` (checked with
commit `7117f86`).

**Singular configurations.** `SerialChain.IsSingular c θ` means that the `6 × n` spatial
Jacobian matrix has rank less than `min 6 n` (p. 123).
For `n ≤ 6` this is linear dependence of the twist columns, equivalently of the body
Jacobian's columns; for `n > 6` it is the library's extension. For the planar two-link
arm, the p. 123 definition gives no singular configuration when the first link length is
nonzero; the folded configurations `sin θ₂ = 0` are singular for the `2 × 2` position
Jacobian `∂p/∂θ` (`Examples.planarTwoLinkPositionJacobian`, in the sense of eq. (3.64)),
which is a different map. Example 3.12 (three parallel coplanar revolute axes) is `SerialChain.isSingular_of_three_parallel_coplanar_revolute`, for every `n ≤ 6`; the elbow manipulator's reference configuration is its printed instance (commit `c2a2604`).

**Manipulability.** The Jacobian of MLS §4.4 (pp. 127–129) is the body Jacobian matrix
`SerialChain.bodyJacobianMatrix` (the book's preference, p. 128). Its singular values are Mathlib's
`LinearMap.singularValues` of `Matrix.toEuclideanLin J`, which uses the standard inner products on
joint rates and on the six coordinates `(v, ω)`: the square roots of the eigenvalues of `JᵀJ` in
decreasing order, indexed from `0`, so `σ_max` is index `0` and `σ_min` (`μ₁`) index `n − 1`;
`μ₂ = σ_min / σ_max` (Lean division, `0` when `σ_max = 0`). These values are not frame invariant:
the spatial Jacobian `Ad_g Jᵇ` has other singular values in general; only the zero sets agree. The
determinant `μ₃` is defined for six joints, on the `6 × 6` matrix with rows `(v, ω)` and columns
joints `1 … 6` in order (columns reindexed by `finSumFinEquiv`), and is the same for the spatial
and body Jacobians because `det Ad_g = 1`. The alternative dextrous workspace (eq. (3.61)) is
`alternativeDextrousWorkspace c Q μ = fk '' {θ ∈ Q | μ θ ≠ 0}`, a set of poses, with the measure
and `Q` explicit; for `0 < n ≤ 6` (six joints for `μ₃`) all three measures give the image of the
nonsingular configurations in `Q`.

**Closed chains.** `ClosedChain n₁ n₂` holds two serial chains in one base and one tool
frame (p. 133). Its joint space `Q′` is the set of
pairs `(θ₁, θ₂)`, each admissible for its chain, with `g₁(θ₁) = g₂(θ₂)` (eq. (3.65)). The
reference tool poses of the two chains are not required to agree; their agreement is
exactly `(0, 0) ∈ Q′`. The differential constraint `J₁ˢθ̇₁ = J₂ˢθ̇₂` (eq. (3.67)) is stated
along trajectories that keep the loop closed near the time considered, and `ρ` (eq. (3.70))
is the dimension of the intersection of the two Jacobian ranges.

**Smoothness of forward kinematics.** Smoothness classes are Mathlib's `ContDiff ℝ k` for every
order `k : WithTop ℕ∞`: `k = ∞` is the book's "smooth" and `k = ω` is analytic, and the theorems
hold for every `k`. A family of rigid motions `x ↦ g(x)` is smooth when every entry of its
homogeneous matrix `[R p; 0 1]` is, which holds exactly when its rotation entries and its translation
are, and exactly when it is smooth in the pose coordinates `(R, p) ∈ ℝ^{3×3} × ℝ³` of the rolling
contact section (`Rolling.contDiff_poseCoords_iff`). Matrix exponentials are stated entry by entry, as
maps into `ℝ^{m×m}`, so that no matrix norm enters a statement; the proofs use the `L^∞` operator
norm with which the library builds its exponentials. The statements concern the coordinate maps,
not `SE(3)` as a manifold (checked with commit `7363824`).

**Jacobians as derivatives.** The partial derivative `∂g_st/∂θᵢ` of MLS eqs. (3.51)–(3.53)
(p. 115) is `SerialChain.fkPartial c θ i`, the `4 × 4` matrix of the derivatives of the entries of
the homogeneous matrix of `g_st` at `θ` in the coordinate direction `i` (`Pi.single i 1`); the
Fréchet derivative is taken entry by entry, with Mathlib's sup norm on `Fin n → ℝ`, so that no
matrix norm enters those statements. The spatial column `ξᵢ'` is `(∂g_st/∂θᵢ g_st⁻¹)^∨` and the
body column `ξᵢ†` is `(g_st⁻¹ ∂g_st/∂θᵢ)^∨`, with the library's `Twist.vee`; the derivative in a
direction `v` is the entry of `(Jˢ(θ)v)^ g_st(θ) = g_st(θ)(Jᵇ(θ)v)^`. Lean index `i` is the
book's `i + 1`. The Fréchet derivative is identified through the trajectory derivative along the
straight joint paths `s ↦ θ + s v`; the matrix-valued trajectory statements keep the `L^∞`
operator norm of the Jacobian module, whose topology is the product topology (checked with commit
`5a650af`).

**Parallel mechanisms.** `ParallelMechanism k n` holds `k` serial chains in one base and one tool
frame, chain `i` with `n i` joints; a configuration is `(i : Fin k) → Fin (n i) → ℝ`, and `Q′`
requires every chain admissible and all forward kinematics equal (eq. (3.65) for `k` chains). The
stacked form (3.68) is the block-diagonal matrix of the spatial Jacobian matrices (rows `(v, ω)`)
against `k` stacked identities. Admissible velocities are the intersection of the `k` Jacobian ranges
and `ρ` its dimension (eqs. (3.69)–(3.70)). For `k = 2` the structure is bridged to `ClosedChain`,
which is unchanged. A kinematic singularity ("the rank of the structure equations drops", p. 134) is a
configuration every neighbourhood of which contains a configuration of `Q′` with a larger `ρ`. With a
set of actuated joints per chain, chain `i` transmits the wrenches (base coordinates, moment about the
base origin) whose pairing with every passive joint's current twist vanishes, passive joints carrying
no torque at static equilibrium (eq. (3.60)); the mechanism is actuator singular when the sums of
transmitted wrenches are not all wrenches (pp. 135, 141).

**Gruebler's count.** Degrees of freedom are counted at the velocity level: `N` moving links (the
ground excluded, as in the four-bar's `N = 3`, p. 136) with velocities in a space of dimension `d`
(`6` spatial, `3` planar), and joint `j` lets the relative velocity of its two bodies range over a
subspace of dimension `fⱼ`. The admissible velocities have dimension at least `dN - ∑ⱼ (d - fⱼ)`, and
"the joints define independent constraints" (p. 133) is read as the constraint map being onto
`∏ⱼ E ⧸ Sⱼ`, which is exactly when the dimension equals the count.

**Self-motions.** The self-motion set of `g_d` is `{θ | g_st(θ) = g_d}` (eq. (3.62)) with no
manifold structure; internal motions are joint trajectories that stay in it near the time
considered, and their rates lie in the null space of the spatial Jacobian. Example 3.17's arm is the
printed position map with angles from `+x`, not a `SerialChain` (checked with commit `7117f86`).

**Denavit–Hartenberg parameters.** `RigidTransform.denavitHartenberg α a d φ` is the transform of
MLS p. 93 with rotation `Rz(φ) Rx(α)` and translation `(a cos φ, a sin φ, d)`; its homogeneous
matrix is the printed one entry by entry. In a `DenavitHartenbergChain` the joint variable is added
to a stored reference value of `φᵢ` (revolute) or `dᵢ` (prismatic), so that `θ = 0` is the
configuration with the stored parameters; the book's identification `φᵢ = θᵢ` is the stored value
`0`. The relative twists of (3.7) are `(0, 0, 0, 0, 0, 1)` and `(0, 0, 1, 0, 0, 0)` in the proximal
link frame, and the chain is read as a `LinkFrameChain`, whose base-frame twists are (3.10).

**Base frames, tool frames and reference configurations.** A new base frame with
`g_{s's} = g` changes the twists to `Ad_g ξᵢ` and the reference tool pose to `g g_st(0)`; the base
frame at the reference tool frame is the case `g = g_st(0)⁻¹`. Taking `θ₀` as the reference
configuration replaces the twists by the columns of `Jˢ(θ₀)` (the joint axes at `θ₀`), the reference
tool pose by `g_st(θ₀)` and the joint space by its translate by `-θ₀`. A new tool frame moving with
the end-effector is `g_{st'} = g_st h` with `h` constant; it changes neither the spatial Jacobian nor
the spatial velocity.

**Resolved rates.** The claim of MLS pp. 117–118 that integrating (3.57) moves the end-effector
from `g₁` to `g₂` is stated with hypotheses the book omits: the workspace path has a derivative at
every time of `[0, T]` (two-sided, the path being defined on the real line), a solution `θ` of
(3.57) on `[0, T]` is given (its existence is a hypothesis), the Jacobian is invertible along it and
`g_st(θ(0)) = g₁`. For a general chain the hypothesis is `Jˢ(θ)θ̇ = Vˢ`; the six-joint form uses the
six rows `(v, ω)` numbered `0, …, 5` in order.

**Redundant manipulators.** `J† = Jᵀ(JJᵀ)⁻¹` (p. 130) is the library's `Composite.rightPinv` of the
six-row spatial Jacobian and is used under full row rank. For the statics (3.63) an end-effector
wrench `Fₑ` applied by the environment, as a body wrench at the tool origin, enters Lagrange's
equations as the generalized force `(Jᵇ)ᵀFₑ`, the joint force whose power is `Fₑ · Vᵇ` (p. 121);
with actuator torques `τ` the generalized force is `τ + (Jᵇ)ᵀFₑ`. Static equilibrium is the
constant motion; the book's `F` in `τ = JᵀF` is the wrench the end-effector exerts, `F = -Fₑ`.

**Spherical joints and the Stewart platform.** A spherical joint about `q` is the rigid motion
`(R, q - Rq)` with `R` free (p. 139), and its velocity is `(-ω × q, ω)`, read as the three columns
`(-eₖ × q, eₖ)` (p. 140); three revolute joints through `q` are a different model with singular
configurations. One leg of (3.72) is `g_s(R_s) e^{ξ̂θ} g_t(R_t) g_st(0)` with `g_t` about the reference
tool pivot `p = g_st(0) q_t` in base coordinates and `ξ = (u, 0)`, `u` the unit reference direction
from `q_s` to `p` (`p ≠ q_s`). The printed `θᵢ = ‖q_si − g_st q_ti‖` (p. 140) is the leg length; the
extension with `θ = 0` at the reference configuration is that length minus `‖p − q_s‖`, recorded as
a corrected printing. "`θᵢ` nonzero" (p. 141) and "`θᵢ > 0`" (Exercise 22(b)) are read as a nonzero
current leg length. The actuated prismatic joints transmit the pure forces `(w, c × w)` along the
current leg directions `w` through the tool pivots `c` (moment about the base origin).

**Chapter 3 worked examples and exercises.** Example 3.4's positions are the printed (3.14) with
angles from `+x`, the dextrous workspace the positions reached with every real orientation `φ`; the
printed "by `2l₃` on the inner and outer edges" is read as moving each edge of the reachable annulus
by `2l₃`, and positive lengths are assumed. Example 3.6's two solutions are the two branches of the
planar solution (3.16) for the point `(y, -x)` of Figure 3.7a's plane (the SCARA's zero configuration
points along `+y`), under its hypotheses. Example 3.10's spanning wrenches assume `l₁l₂ sin θ₂ ≠ 0`.
The Stanford arm of Example 3.9 has its joint axes read from Figure 3.14 and the printed `ωᵢ'`, with
the tool frame at the wrist centre. Exercise 13 is read with the `2 × 2` position Jacobian and
condition number `1` as `JᵀJ = σ²I`, `σ ≠ 0`. Exercise 14's chains are rotation-only chains of
three revolute joints through the origin, singular in the sense of p. 123. Exercise 18 is answered
for the library's measures, which use the body Jacobian. The Gruebler counts of Exercises 20–22 read
the links and joints from the printed figures: the slider–crank's bar `l₃` is rigid with the slider,
a pin joining three links counts as two joints, and each Stewart leg is two bodies joined by the
prismatic joint.

**Spherical wrists.** A chain of `n + 3` joints has a spherical wrist (`SerialChain.HasSphericalWrist`)
when its last three joints (Lean indices `n + i`) are revolute with unit axes `ω₀, ω₁, ω₂` through the
reference tool position `p_st(0)`, with `ω₀ ⊥ ω₁` and `ω₁ ⊥ ω₂`. This is MLS p. 96's "three orthogonal
revolute axes which intersect at a point" with "the end-effector frame … placed at the origin of the
wrist axes"; the third orthogonality is not needed. The workspace statements `W_D = W_R` and
`W = W_R × SO(3)` are for the unrestricted joint space. The three-axis angles onto `SO(3)` need only
the two consecutive orthogonalities, so ZYZ and mutually orthogonal wrists are covered alike.

**Chapter 3 exercises, continued.** Subproblem 4's hint (Exercise 6) is counted for non-collinear
centres, "at most two points" stated as: among any three common points two are equal. Exercise 13(b)
reads "elbow manipulator without a wrist" as the first three joints of Example 3.2 and the Jacobian
as the `3 × 3` Jacobian of the wrist-centre position `p(θ)` (the derivative of the printed position),
with condition number `1` as `JᵀJ = σ²I`, `σ ≠ 0`; Exercise 13(c) is recorded through the statics
`τ = Jᵀf`: at an isotropic configuration `‖Jᵀf‖ = |σ| ‖f‖` for every `f`.

**Parallel exercises.** The slider–crank of Exercise 20 is two chains in one base frame at the crank
pivot and one tool frame on the slider block: the linkage, with revolute joints about `+z` through
`(0, 0, 0)`, `(l₁, 0, 0)`, `(l₁ + l₂, 0, 0)` and `g_st(0) = (I, (l₁ + l₂ + l₃, 0, 0))` (stretched
along the slide line, angles counterclockwise, so the figure's clockwise `θ₂` is negative), and the
slide, prismatic along `+x` with `g_st(0) = I`, whose coordinate is the printed distance `d`.
Actuation is a set of joints per chain, read by `ParallelMechanism.transmissibleWrenches`; with the
slide actuated nothing is actuator singular, so the dead centres appear as kinematic singularities.
The variable geometry truss of Exercise 21 has base pivots `(0, ±h/2)` and platform pivots at the same
spacing; leg `i` has coordinates `(α, d, β)`: the leg direction from `+x`, the signed leg length (no
actuator limits) and the platform angle relative to the leg; its zero configuration is every leg of
length `0` along `+x`, which lies in `Q′` only for `h = 0`. Planar twists are the twists
`(v_x, v_y, 0, 0, 0, ω)`. The Stewart platform with U-joints of Exercise 22(c)–(d) has legs of five
joints (two revolute joints through each pivot, the prismatic joint between); "singular" in
Exercise 22(d) is read as a configuration where some tool twist is not admissible (p. 134), which
holds everywhere since `ρ ≤ 5`.

**The manipulators of Figure 3.23.** The figure carries no dimensions and is an oblique projection
(`x` right, `z` up, depth `y` at `45°`). Base frame at the marked point where the axes of `θ₁` and
`θ₂` meet, `z` along `θ₁`, `y` along the drawn axis of `θ₂`, `x` along the arm in the drawn
configuration, which is `θ = 0`; tool frames parallel to the base frame; positive rotations by the
right-hand rule about the drawn axis directions. (i): axes `z`, `y`, `x` through the origin, tool at
`(l₁, 0, 0)`; (iii): axes `z`, `y` through the origin and `y` through the elbow `(l₁, 0, 0)`, tool at
`(l₁ + l₂, 0, 0)`; (iv): axes `z`, `y` and a prismatic joint along `x`, tool at `(l₁, 0, 0)` for
`θ₃ = 0`; (ii): axes `z`, `y` and a third axis `(cos γ, 0, sin γ)` through `(a, 0, 0)` in the vertical
plane of the arm, read from the elliptical caps of its cylinder (cylinders along the depth axis are
drawn with circular caps) and from the second marked point on the axis of `θ₁`, which the third
axis meets at `(0, 0, −a tan γ)`; the figure draws `γ = 45°`; tool at `(l, 0, 0)`.

**Evidence scope.** The declarations named here were elaborated and audited for axioms with
commit `3e5bdd1`, and the `lake build` of `RoboLean.lean` was checked
separately. K13 and the planar workspace rows were checked with commit `f237457`, built against
the `Twist` structure. The subproblem, singularity and closed-chain declarations were checked with commit `fc99877`, and the manipulability and elbow-manipulator declarations with commit `c2a2604`.

## Dynamics conventions


Recorded 2026-10-09 10:11:43 UTC with commit `18f4de2`. Source: MLS Chapter 4, printed pp. 161–178, read
as text and, for pp. 162, 168, 176–177, as rendered images. These are conventions of the
Lean model; they do not certify a physical robot or its inertial parameters.

**Generalized inertia and block order.** A generalized inertia is a real matrix indexed by
`Fin 3 ⊕ Fin 3`, the index type of `Twist.coordinates` and `Twist.adjointMatrix`: `Sum.inl` is
the linear block, `Sum.inr` the angular block. MLS eq. (4.9), p. 162, prints
\(\mathcal M=\begin{bmatrix} mI&0\\0&\mathcal I\end{bmatrix}\) acting on \(V^b=(v^b,\omega^b)\), linear first;
this is the library's twist order, so no transposition is needed.
`RigidBody.generalizedInertia m 𝓘 = fromBlocks (m • 1) 0 0 𝓘`.

**Frame of the inertia.** A generalized inertia refers to a body-fixed frame, and the kinetic
energy `RigidBody.kineticEnergy 𝓜 V = ½ V·𝓜V` pairs it with the body velocity of that same frame;
the types do not enforce the match. The block-diagonal form is the generalized inertia in a
frame at the mass center (MLS pp. 161–163). In another body-fixed frame `C` with constant pose
`g = g_BC` relative to `B`, the generalized inertia is `transformInertia g 𝓜 = Ad_gᵀ 𝓜 Ad_g`,
because \(V^b_C=\operatorname{Ad}_{g^{-1}}V^b_B\) (MLS Proposition 2.15, p. 59); MLS eq. (4.28) is
the case `g = g_{sl_i}(0)⁻¹`. For a pure translation `g = (I, p)` the result is
\(\begin{bmatrix} mI& m\widehat p\\ -m\widehat p& \mathcal I-m\widehat p^{\,2}\end{bmatrix}\)
(`RigidBody.transformInertia_translation`).

**Link frames of an open chain.** `InertialChain n` holds a `SerialChain n`, the reference poses
\(g_{sl_k}(0)\) and the generalized inertias \(\mathcal M_k\), each in its own link frame. Lean link
`k : Fin n` is the link distal to Lean joint `k` (the book's link `k + 1`) and is moved by Lean
joints `0..k`: \(g_{sl_k}(\theta)=e^{\widehat\xi_0\theta_0}\cdots e^{\widehat\xi_k\theta_k}g_{sl_k}(0)\)
(p. 168). This is the forward kinematics of `linkChain k`, the chain whose later joints have twist
`0`; its body Jacobian is the book's \(J^b_{sl_k}=[\xi^\dagger_0\cdots\xi^\dagger_k\;0\cdots0]\). The
6×n matrix `linkJacobianMatrix` has rows `Twist.coordinates`, like `spatialJacobianMatrix`.

**Mass matrix and kinetic energy.** \(M(\theta)=\sum_kJ_k^{\mathsf T}\mathcal M_kJ_k\) (eq. (4.19)) and
\(T=\tfrac12\dot\theta^{\mathsf T}M(\theta)\dot\theta\) (eq. (4.18)). Joint rates are real vectors `Fin n → ℝ`.

**What positivity is assumed and what is proved.** Assumed, as explicit hypotheses: symmetry of
`𝓘` or `𝓜_k`; `0 ≤ m` or `0 < m`; positive (semi)definiteness of `𝓘` or `𝓜_k`; and, for strict
positivity of `M(θ)`, either injectivity of the stacked Jacobian or nonzero joint twists (for
example `IsRevoluteJoint`/`IsPrismaticJoint`). Proved: symmetry, semidefiniteness and
definiteness of `𝓜`, of `Ad_gᵀ𝓜Ad_g` and of `M(θ)` from those hypotheses, and the converse that
with PD link inertias `M(θ)` is PD only if the stacked Jacobian is injective. Not addressed:
derivation of `𝓘` from a mass density, physical realizability of inertial parameters, and any
numerical conditioning.

**Units.** Masses, lengths, times and inertias are real numbers; units (for example kg, m, s,
kg·m²) are chosen by the model's author and are not tracked by types. The linear and angular blocks
of a twist carry different units, so `𝓜` is the only metric used here on twists; `Twist` carries no norm.

**Christoffel symbols and the Coriolis matrix.** For partial derivatives `dM k = ∂M/∂θₖ`,
`Christoffel.symbol dM i j k = (dM k i j + dM j i k − dM i k j)/2` (eq. (4.22)),
`coriolisMatrix dM θ̇ i j = Σₖ Γᵢⱼₖ θ̇ₖ` (eq. (4.23)), and `rate dM θ̇ = Σₖ θ̇ₖ • dM k` (`Ṁ` by the
chain rule). Derivative data are inputs: either the family `dM`, or Fréchet derivatives
`M' i j : (Fin n → ℝ) →L[ℝ] ℝ` of the entries at a configuration, read as
`partials M' k i j = M' i j eₖ`. The skew symmetry of `Ṁ − 2C` (Lemma 4.2(2)) depends on this
choice of `C` (as MLS notes on p. 171) and on symmetric partials, which follow from `M` symmetric at
every configuration.

Recorded 2026-10-10 01:05 UTC with commit `f042580`. Source: MLS
printed pp. 155-178 and p. 209 (Exercise 8), read as text; p. 175 rendered.

**Lagrange's equations (Theorem 4.1, p. 158).** A Lagrangian is a real function
`L : (Fin n → ℝ) → (Fin n → ℝ) → ℝ` of configuration and velocity. Its partial derivatives
`∂L/∂q̇ᵢ` and `∂L/∂qᵢ` at `(q, v)` are the one-variable derivatives at `0` of
`s ↦ L(q, v + s eᵢ)` and `s ↦ L(q + s eᵢ, v)` (`Lagrangian.velocityPartial`,
`Lagrangian.positionPartial`). `LagrangeEquationsAt L θ Υ t` means: for every `i`, the function
`s ↦ ∂L/∂q̇ᵢ(θ(s), θ̇(s))`, with `θ̇ = deriv θ`, has an actual derivative at `t` equal to
`∂L/∂qᵢ(θ(t), θ̇(t)) + Υᵢ`. The existence of that derivative is part of the statement. MLS proves
nothing here (it cites [99]); the predicate is a definition, not a derived law of mechanics.

**Mechanical Lagrangian and equations of motion (pp. 169-171).**
`Lagrangian.mechanical M V q v = ½ vᵀ M(q) v − V(q)`. The gradient of a potential is read from
Fréchet derivative data `V'`, \((\partial V/\partial q)_i = V'(e_i)\) (`Lagrangian.gradient`), in
the style of `Christoffel.partials`. With `M(q)` symmetric everywhere, Lagrange's equations are
equivalent to
\(M(\theta)\ddot\theta + C(\theta,\dot\theta)\dot\theta + \partial V/\partial\theta = \Upsilon\),
with `C` the Christoffel matrix of (4.23). For (4.24) the generalized force is split as
\(\Upsilon = \tau - N_e\) (actuator torques minus further joint forces such as viscous friction
\(N_e = \beta\dot\theta\)), giving \(N = \partial V/\partial\theta + N_e\). The energy is
\(H = \tfrac12\dot\theta^{\mathsf T}M(\theta)\dot\theta + V(\theta)\), and along solutions
\(\dot H = \dot\theta^{\mathsf T}\Upsilon\) (Exercise 8, p. 209).

**Gravity (pp. 169, 174).** Gravity is uniform, given by a scalar `g` and a vector `up` in base
coordinates pointing opposite to gravity, so the gravitational acceleration is `−g • up`. The
height of a point `p` is `⟪up, p⟫`; `up` is meant to be a unit vector, and no theorem needs that.
The mass center of link `k` is the origin of its link frame (p. 168), so
\(h_k(\theta) = \langle up, p_k(\theta)\rangle\) with \(p_k\) the translation of
\(g_{sl_k}(\theta)\). The masses are an explicit argument `m : Fin n → ℝ`, not read from the
generalized inertias. `gravityTerm` is `∂V/∂θ`, defined through `fderiv`. `V` is proved
differentiable for every chain, so the `fderiv` junk value is never reached, and `gravityTerm`
equals the Jacobian form \(\sum_k m_k g \langle up, \omega_{ik}\times p_k + v_{ik}\rangle\), with
\((v_{ik}, \omega_{ik})\) column `i` of the spatial Jacobian of link `k`. In the library's examples
`up = Rotation.zAxis`.

**Newton-Euler equations and the coadjoint sign (pp. 165-167).** The body frame is at the mass
center. A body velocity `V = (v, ω)` and a body wrench `F = (f, τ)` at the mass center use the
twist and wrench orders. The momentum `momentum m 𝓘 V = (m v, 𝓘 ω)` is a `Wrench` with
coordinates `generalizedInertia m 𝓘 *ᵥ V.coordinates`. The body acceleration is a twist `A` whose
linear and angular parts are actual derivatives of those of `V`, because `Twist` carries no
topology. (4.16) is `momentum m 𝓘 A + gyroscopic m 𝓘 V = F` with
`gyroscopic = (ω × m v, ω × 𝓘ω)`. The library's twist bracket is
`Twist.bracket V η = (ω_V × v_η − ω_η × v_V, ω_V × ω_η)`, the vee of \(\hat V\hat\eta − \hat\eta\hat V\),
with matrix `adMatrix V = [[ω̂, v̂], [0, ω̂]]` on six coordinates. Its transpose with respect to the
power pairing is `coadjoint V F = (−ω × f, −v × f − ω × τ)` (`pair (coadjoint V F) η = pair F [V, η]`).
In this convention `gyroscopic = −coadjoint V (𝓜V)`, so (4.16) reads
\(\mathcal M\dot V - \operatorname{ad}_V^{\mathsf T}(\mathcal M V) = F\). The gyroscopic term pairs
to zero with `V`, which gives the power balance
\(\tfrac{d}{dt}\tfrac12 V^{\mathsf T}\mathcal M V = F\cdot V\) for symmetric `𝓘`.

**Euler's equation in spatial coordinates and the derivation of (4.14)–(4.16) (pp. 166–167, Exercise 4).** The rotation curve `R(t)` has actual derivative data, `ωˢ` is the library's spatial angular velocity (2.48) at `t` and `ωᵇ = Rᵀωˢ` the body one; `I′ = R𝓘Rᵀ` acts on vectors as `R(𝓘(Rᵀ·))`. Newton's law (4.12) is `f = d/dt(mṗ)` and Euler's law is `τ = d/dt(I′ωˢ)`, with `f`, `τ` applied at the mass center in inertial coordinates; their expansions are `mv̇ᵇ + ωᵇ × mvᵇ = Rᵀf` for `vᵇ = Rᵀṗ` and (4.13) `I′ω̇ˢ + ωˢ × I′ωˢ = τ`, and `ω̇ᵇ = Rᵀω̇ˢ`. For a pose curve the body velocity `Vᵇ` is `RigidTransform.bodyVelocity`, and (4.16) (`NewtonEulerEquation`, still the library's definition) holds with the body acceleration `(v̇ᵇ, Rᵀω̇ˢ)` and `Fᵇ = (Rᵀf, Rᵀτ)` exactly when the inertial-frame laws do. `𝓘` needs no symmetry. Exercise 3's frame change `Ad_{g_bc}ᵀ𝓜Ad_{g_bc}` uses the twist order `(v, ω)` as printed. Viscous friction (p. 170) is `N = ∂V/∂θ + βθ̇` with one `β`, and an end-effector force `F` enters as `−JᵀF` in `N`, so that the right side reads `τ + JᵀF`. Exercise 5 is read as the balance of the spatial momentum `(mṗ, I′ωˢ + p × mṗ)` (linear momentum and angular momentum about the origin of the inertial frame) with the wrench moved to the origin, `(f, τ + p × f)`. Exercise 1's figures are read with `θ` from the downward vertical, a massless pivot on the wire (`q = (x, θ)`, the wire as the `x`-axis, `y` up), and for the double pendulum `θ₁` from the downward vertical and `θ₂` relative to the first link, point masses at the link ends.

**Derivatives of the inertia matrix (Prop. 4.3, pp. 175-177).** `massMatrixDeriv θ i j` is the
Fréchet derivative at `θ` of `q ↦ M(q)ᵢⱼ`. It exists for every chain, and
`Christoffel.partials (massMatrixDeriv θ) k = ∂M/∂θₖ`. Only first-order differentiability is
established. The book's \(A_{lj}\) (4.27) is the adjoint of the rigid motion
`relativeMotion l j θ`, the inverse of the product of the joint motions strictly after joint `j`
up to joint `l`, for `j ≤ l` (Lean indices). The case \(A_{lj} = 0\) for \(l < j\) is not
represented, and the sums are restricted to \(l \ge \max(i,j)\). Internally the proofs use the
operator norm on homogeneous matrices (`Matrix.Norms.Operator`); every public statement concerns
real-valued entries and does not depend on that choice. Evidence: the build
and axiom audit of commit `f042580`.

**Mass distributions and the inertia tensor (pp. 161–163; commit `7854d59`).** A mass distribution is a
measure `μ` on `Vec3`, the body-frame coordinates `r` of body points (the book's `ρ(r) dV` on
`V`); it is nonnegative by type, and a density `ρ ≥ 0` is the case `volume.withDensity ρ`. The
mass is `μ(univ)` as a real number (`RigidBody.mass`, `0` for an infinite measure), the center of
mass is `(1/m)∫ r dμ` (`RigidBody.centerOfMass`), and the inertia tensor is
`𝓘 = −∫ r̂² dμ`, defined entrywise, `𝓘ᵢⱼ = −∫ (r̂r̂)ᵢⱼ dμ = ∫ (‖r‖²δᵢⱼ − rᵢrⱼ) dμ`
(`RigidBody.inertiaTensor`), with Mathlib's Bochner integral; it is a real `3 × 3` matrix in the
body frame, the `𝓘` argument of `generalizedInertia`. The origin of the body frame need not be
the center of mass. Where integrals must exist, theorems assume `Integrable (‖r‖²) μ`. For such
distributions the hypotheses that the generalized inertia places on `𝓘` mean: symmetric always; positive
semidefinite always; positive definite exactly when `μ` is not concentrated on a line through
the body-frame origin (`inertiaTensor_posDef_iff`). The homogeneous bar of Example 4.2 is
`(m/(lwh))·volume` on the box `[−l/2, l/2] × [−w/2, w/2] × [−h/2, h/2]` (length along `x`).

**The kinetic energy from the volume integral, homogeneous bodies and the change of body frame (pp. 161–163, (4.8)–(4.9); p. 208, Exercises 2 and 3).** The kinetic energy of a mass distribution `μ` along a pose trajectory is `T = ½ ∫ ‖ṗ + Ṙ r‖² dμ` (`RigidBody.kineticEnergyIntegral`), with `ṗ` the translation column and `Ṙ` the rotation block of the actual derivative of the homogeneous pose; the body velocity is the library's `RigidTransform.bodyVelocity` (twist order `(v, ω)`). For a body frame anywhere `T = ½ (Vᵇ)ᵀ [[m I, −ĉ], [ĉ, 𝓘]] Vᵇ` (`RigidBody.distributionInertia`), with `c = ∫ r dμ = m r̄` and `𝓘` about the frame origin; at the mass center (`c = 0`) this is (4.9). The integrals assume a finite distribution (positive mass) with integrable second moment. A homogeneous body of mass `m` on a region `V` is `(m / vol V) · volume|_V` (`RigidBody.homogeneousDistribution`); the bar of Example 4.2 is the case with the density written as `m/(lwh)`. The ellipsoid of Exercise 2(a) is `{(x/a)² + (y/b)² + (z/c)² ≤ 1}` with the frame at its center along the semi-axes, and the cylinder of Exercise 2(b) is `{x² + y² ≤ r², |z| ≤ h/2}` with the frame at its center and `z` along the axis; no density, mass or frame is printed. For Exercise 3 the body seen from a second frame `C` with `g_bc = (R, p)` (the rigid motion taking `C` to `B`) is the image of `μ` under `r ↦ g_bc⁻¹ r = Rᵀ(r − p)` (`RigidBody.reframeDistribution`).

**The bracket formula (4.30) (pp. 176–177; commit `7854d59`).** MLS's `A_{lj}` (4.27), including the printed
case `A_{lj} = 0` for `l < j`, is `InertialChain.relativeAdjoint l j θ`: the adjoint of
`relativeMotion l j θ` (the inverse of the product of the joint motions strictly after joint `j`
up to joint `l`) for `j ≤ l`, and `0` otherwise. With the library bracket `Twist.bracket`, the vee
of `ξ̂₁ξ̂₂ − ξ̂₂ξ̂₁` (the book's (4.26)), the printed formula holds as printed:
`∂Mᵢⱼ/∂θₖ = ∑_{i ≤ l, j ≤ l} ((Aₗₖ[Aₖᵢξᵢ, ξₖ])ᵀ𝓜'ₗ(Aₗⱼξⱼ) + (Aₗᵢξᵢ)ᵀ𝓜'ₗ(Aₗₖ[Aₖⱼξⱼ, ξₖ]))`
in Lean indices (book minus one), with pairings in six coordinates and `𝓜'ₗ =
transformInertia (linkRef l)⁻¹ (linkInertia l)`. `∂/∂θₖ` is the derivative along the coordinate
line `θ + s eₖ`, i.e. `massMatrixDeriv θ i j eₖ = Christoffel.partials (massMatrixDeriv θ) k i j`.
The proof splits `relativeMotion l j` at joint `k` (`g_{lj}(θ + s eₖ) = g_{lk}(θ) exp(−sξ̂ₖ)
g_{kj}(θ)` for `j < k ≤ l`) and uses `d/ds Ad_{exp(−sξ̂)} η |₀ = [η, ξ]`.

**Frame freedom of the link frames (p. 168, eq. (4.28); commit `7854d59`).** `InertialChain.reframe ch h`
moves the frame of link `k` by the constant body-fixed transform `h k` (reference pose
`g_{sl_k}(0) h_k`) and re-expresses its inertia as `transformInertia (h k)`, that is
`Ad_{h_k}ᵀ 𝓜_k Ad_{h_k}`; the link body Jacobian becomes `Ad_{h_k⁻¹} J_k` and `M(θ)` is unchanged
(`massMatrix_reframe`). So the choice of the link frames, in particular placing them at the mass
centers, does not affect `M(θ)` once the inertias are moved with them. `linkJacobianMatrix k θ` is
`(linkChain k).bodyJacobianMatrix θ` by definition (`linkJacobianMatrix_eq_bodyJacobianMatrix`).

## Stability and control conventions

Recorded 2026-10-10 02:08 UTC with commit `70fcc3b`. Source: MLS printed
pp. 179–199, read as text; pp. 182, 191, 193, 194 rendered.

**Systems and solutions (p. 179).** A system `ẋ = f(x, t)` is `f : ℝ → E → E` with time first,
`f t x`; likewise a Lyapunov function is `V : ℝ → E → ℝ`, `V t x`. `E` is a real normed space; for
`Fin n → ℝ` and products the norm is Mathlib's sup norm (maximum of the components), so
quadratic forms are compared with `‖x‖²` through compactness of the unit sphere
(`QuadraticBounds`), not through eigenvalues. A solution from `t₀` (`Stability.IsSolution f t₀ x`)
is continuous on `[t₀, ∞)` and has the actual derivative `f t (x t)` at every `t > t₀`. Initial
times are `t₀ ≥ 0` (MLS's `ℝ₊`). Every stability notion quantifies over all solutions, so a
stability theorem by itself says nothing about whether solutions exist. An autonomous system
`ẋ = f(x)` (eq. (4.46)) is written `fun _ => F`. (commit `9968ea8`)

**Solution flows (pp. 179, 188).** Where existence matters (Lasalle's principle and its
applications), it is the hypothesis `Stability.HasFlow F φ` for an autonomous field `F`: `φ 0 x = x`;
`t ↦ φ t x₀` solves the system from time `0`, so `t ↦ φ (t − t₀) x₀` (MLS's `s(t, x₀, t₀)`) solves
it from every `t₀`; every solution from `t₀ ≥ 0` equals `t ↦ φ (t − t₀) (x t₀)` on `[t₀, ∞)`; each
`φ t` with `t ≥ 0` is continuous. Only forward time is used; joint continuity in `(t, x)` and
backward solutions are not required, so Mathlib's two-sided `Flow ℝ E` is not used. The interface
presupposes solutions for all forward time. A flow is constructed for every globally Lipschitz `F`
on a Banach space (`exists_hasFlow_of_lipschitzWith`, commit `f926ad4`), for every locally Lipschitz `F` on a
proper space with a Lyapunov function whose sublevel sets are compact and which does not increase
along local solutions (`exists_hasFlow_of_lyapunov`, commit `f926ad4`), and explicitly for linear fields
(`exp(t A)`, `hasFlow_linear`); shifting the state shifts the flow (`HasFlow.comp_sub_const`).
"Local solution" means Mathlib's form: `HasDerivWithinAt γ (F (γ s)) (Icc 0 T) s` for `s ∈ [0, T]`.

**ω-limit and invariant sets (Definitions 4.7–4.8, p. 188).** The ω-limit set of the trajectory
from `x₀` is Mathlib's `omegaLimit atTop φ {x₀}`, equal to MLS's set of limits along strictly
increasing times `tₙ → ∞`; it does not depend on the initial time. "Invariant" means positively
invariant, Mathlib's `IsForwardInvariant φ M` (`φ t` maps `M` into `M` for `t ≥ 0`). The largest
invariant set inside `S` is `largestInvariantSubset φ S`, the union of the invariant subsets of
`S`; under a flow it is the set of points whose forward trajectory stays in `S`. "The trajectory
tends to `M`" is formalized as: it eventually enters every open set containing `M` (and its
ω-limit set is nonempty and contained in `M`).

**Lasalle's principle (Theorem 4.7, p. 188).** `V` is time-invariant and continuous, `V̇` is its
derivative along solutions (`HasDerivAlongSolutions` with `fun _ => V`), continuous on
`Ω_c`, and `Ω_c = {V ≤ c}` is compact (`IsCompact`). The principle is proved for compact
positively invariant sets and, in MLS's sublevel form, for trajectories starting in `{V < c}`:
a trajectory starting on the level `{V = c}` may leave `Ω_c` when `V̇ ≤ 0` holds only on `Ω_c`.

**Tracking errors (§5, p. 190).** For a reference `x_d` with derivative `x_d'`, the error system is
`Stability.errorSystem f x_d x_d'`, `ż = f(t, z + x_d(t)) − x_d'(t)`; its solutions are exactly
`x − x_d` for the solutions `x` of `f`. Exponential trajectory tracking is exponential stability
of its origin (Definition 4.3) or the explicit bound
`‖(e(t), ė(t))‖ ≤ m e^{−α(t − t₀)} ‖(e(t₀), ė(t₀))‖` on the closed-loop state.

**Local Lasalle (Theorem 4.7, "in particular", p. 188; Example 4.7, p. 189).** Besides the
sublevel form, `asymptoticallyStableAt_of_lasalle_ball` asks `V` locally positive definite,
`V̇ ≤ 0` and continuous on a ball, and the largest invariant set in `{x ∈ ball : V̇ = 0}` inside
`{0}`; it needs no compact sublevel set (a proper state space suffices). Example 4.7 uses it on
the ball of radius `σ₀` in place of MLS's `Ω_c`.

**Passivity (Example 4.6, p. 187).** `IsPassiveOn h σ₀`: `σ h(σ) ≥ 0` for `|σ| ≤ σ₀`, with equality
there only at `σ = 0`. With continuity it gives `h(0) = 0`. MLS's "smooth" is read as continuous.

**Proposition 4.10 (p. 194).** The augmented PD law (4.53) is `augmentedPDTorque`; the closed loop
is (4.54) at each time. `V = ½ ėᵀM(θ)ė + ½ eᵀK_pe + ε eᵀM(θ)ė` with `θ = θ_d(t) + e`;
`Ṁ(θ, θ̇) = ∑ₖ θ̇ₖ ∂M/∂θₖ` (`Mdot`) from the actual partial derivatives of `M`; the derivative along
(4.54) is `−ėᵀ(K_v − εM)ė − ε eᵀK_pe + ε eᵀ(−K_v + Ṁ − C)ė`, not the printed `½Ṁ` in the last
term. Bounds are stated with the sup norm, on the tube `‖(e, ė)‖ ≤ R` around `(θ_d, θ̇_d)`; the
smallness of `ε` is the pair of explicit inequalities `2εμ ≤ min(λ, k_p)` and
`ε(2k_pμ + (κ_v + c)²) ≤ k_p k_v`. The formal conclusion is semiglobal (rate depending on the
bound of initial errors), global for constant inertia.

**Named exponential constants and arrival times (Definition 4.3, p. 180; p. 195).**
`Stability.ExponentialBoundOn f x* C α ρ` is the bound (4.34) with its constants named: `C, α > 0`,
and every solution from a time `t₀ ≥ 0` with `‖x(t₀) − x*‖ < ρ` (strict) satisfies
`‖x(t) − x*‖ ≤ C e^{−α(t − t₀)} ‖x(t₀) − x*‖` for `t ≥ t₀`. `ExponentiallyStable` is its existence
for some `ρ > 0`, and `GloballyExponentiallyStable` gives it for every `ρ`. The arrival time for a
tolerance `ε` is `arrivalTime C α ρ ε = max(0, log(Cρ/ε)/α)` with the natural logarithm. A
constant set point is the trajectory `θ_d(t) ≡ θ_d` with `θ̇_d ≡ θ̈_d ≡ 0`, under which (4.53) is the
PD law with compensation of `N` (`pdCompensatedTorque`); the remark of p. 195 calls it (4.51),
without `N`. The set-point result is semiglobal and uniform in the set point (checked with commit
`5a650af`).

**Converse of Theorem 4.5 (p. 183).** For an autonomous system with a globally Lipschitz field on a
Banach space, exponential stability is equivalent to a continuous time-invariant `V` with the
first three bounds of the theorem on a ball (`exponentiallyStable_iff_exists_quadratic_lyapunov`);
`V(x) = ∫₀^T ‖φ(τ, x)‖² dτ`. The fourth bound is not part of that statement; with all four bounds the converse holds for time-varying fields with a differentiable flow (paragraph "Differentiable flows" below).

**Global notions and Theorem 4.4(4) (pp. 180, 183).** `GloballyAsymptoticallyStableAt f xe t₀`:
stable at `t₀` and every solution from `t₀` converges to `xe`. `GloballyUniformlyAsymptoticallyStable`:
uniformly stable, uniformly bounded and uniformly globally attractive (one time `T` for every
`r, η > 0`, all `t₀ ≥ 0` and all solutions starting within `r`). The uniform global conclusion
of Theorem 4.4(4) is proved with `V ≤ β(‖x‖)` for all `x`; with MLS's local decrescence the
theorem gives uniform asymptotic stability and global asymptotic stability at every `t₀`.

**Stability notions (Definitions 4.1–4.3).** `StableAt f xe t₀` and `AsymptoticallyStableAt` are
pointwise in `t₀`; `UniformlyStable` and `UniformlyAsymptoticallyStable` take `δ` (and the
convergence time) independent of `t₀ ≥ 0` and of the solution; `ExponentiallyStable` takes
`m, α, ε` independent of `t₀ ≥ 0`. An equilibrium `xe ≠ 0` is handled through `shift f xe`,
whose origin has the same stability (`stableAt_shift_iff`), as MLS does on p. 179.

**Lyapunov candidates (Definitions 4.4–4.6).** The comparison functions `α`, `β` are continuous
and strictly increasing on `[0, ∞)` and vanish at `0` (`IsClassK`); MLS does not state `α(0) = 0`,
which is added. "`V̇` along the trajectories" is the hypothesis `HasDerivAlongSolutions f V Vdot U`
(along every solution while it is in `U`, `d/dt V(t, x(t)) = Vdot(t, x(t))`); for a Fréchet-
differentiable `V` it holds with `Vdot = ∂V/∂t + ∂V/∂x f`.

**The manipulator as a system (eq. (4.47)).** `ManipulatorModel n` bundles an `InertialChain n`,
link masses, `g`, `up` and further joint forces `Nₑ(θ, θ̇)`; `N = ∂V/∂θ + Nₑ`. The equations of
motion are Lagrange's equations for `L = T − V` with generalized force `τ − Nₑ` (the predicate `Lagrangian.LagrangeEquationsAt`),
equivalent to (4.47) with symmetric link inertias. The state is `(θ, θ̇) ∈ ℝⁿ × ℝⁿ`; under a feedback
law `τ = u(t, θ, θ̇)` the closed loop is `f(t, (q, v)) = (v, M(q)⁻¹(u − C(q, v)v − N(q, v)))` with
Mathlib's `Matrix.inv`, used only under the hypothesis that `M(q)` is positive definite.

**Gains and control laws (§5).** Gains are real `n × n` matrices; "positive definite" is Mathlib's
`Matrix.PosDef`, which includes symmetry (MLS writes `K > 0`). Computed torque is (4.49) with a
desired trajectory given by `θ_d` and actual derivatives `θ_d'`, `θ_d''` at every time. The PD
set-point law formalized is `τ = N(θ, θ̇) − K_v θ̇ − K_p(θ − θ_d)` (compensation of `N`, (4.53) with
`θ̇_d ≡ 0`); the bare law (4.51) is defined and shown to have `θ_d` as a rest point only where
`N(θ_d, 0) = 0`. Exact cancellation of the model is assumed throughout; sampled implementation,
actuator limits and model error are outside these statements. For the asymptotic stability of the compensated PD law (Proposition 4.9 as formalized), `M` is
uniformly positive definite, `λ‖v‖² ≤ vᵀ M(q) v` for one `λ > 0` and all `q, v` (MLS p. 191's
phrase; it makes the sublevel sets of `½ θ̇ᵀ M θ̇ + ½ eᵀ K_p e` compact), `K_v` is positive
definite, and the closed loop `ManipulatorModel.pdClosedLoop` has a solution flow; for constant inertia the closed
loop is linear and its flow is constructed; since commit `f926ad4` the flow is constructed for every locally
Lipschitz closed loop with uniformly positive definite `M` (the energy traps the solutions), in
particular for the planar two-link arm, whose closed loop is `C¹`.

**Workspace dynamics (Lemma 4.11).** A workspace parametrization is a map
`f : ℝⁿ → ℝⁿ` (`(Fin n → ℝ) → Fin n → ℝ`, the book's `n = p`, p. 196) of class `C²` on all of
`ℝⁿ`; MLS's "smooth and invertible" is replaced by the hypothesis its proofs use, `J(θ)` invertible
(`IsUnit (jac f θ).det`), assumed only at the configurations where `J⁻¹` is used: at `θ(t)` for the
pointwise statements and at `θ(s)` for every `s > t₀` along a tracking solution, never globally
(the planar arm's xy map is singular at `sin θ₂ = 0`). `J = MapJacobian.jac f θ` is the matrix of
the Fréchet derivative of `f` (column `j` is `Df(θ) e_j`); it is not the manipulator Jacobian of
Chapter 3. `J̇ = MapJacobian.jacDot f θ θ̇` is the matrix of the second derivative `D²f(θ)(θ̇, ·)`,
the actual derivative of `J(θ(t))`. Derivatives of matrix-valued curves are stated entry by entry;
the inverse is `Matrix.inv`. The effective parameters are functions of `(θ, θ̇)`: `M̃ = J⁻ᵀMJ⁻¹`,
`C̃ = J⁻ᵀ(C − MJ⁻¹J̇)J⁻¹` (equal to the printed `J⁻ᵀ(CJ⁻¹ + M(d/dt)J⁻¹)` along every motion),
`Ñ = J⁻ᵀN`; (4.55) is read with `ẋ = Jθ̇` and `ẍ = J̇θ̇ + Jθ̈`. `M̃˙` is
`X'ᵀMX + XᵀṀX + XᵀMX'` with `X = J⁻¹`, `X' = −XJ̇X` (`workspaceMdot`). The workspace computed
torque law is `τ = Jᵀ(M̃(ẍ_d − K_vė − K_pe) + C̃ẋ + Ñ)` with `e = f(θ) − x_d`, `ė = Jθ̇ − ẋ_d`
(MLS prints `Cẋ + N`, for which the error equation fails); exponential tracking is the bound on
`‖(e, ė)‖` (sup norm) for every closed-loop solution on the joint state `(θ, θ̇)` along which `J`
stays invertible. The workspace PD law is the set-point extension of Proposition 4.9 (paragraph "Workspace PD law" below). In the planar example the workspace map is
the end-effector xy position in the frame of the dynamic arm `planarTwoLinkArm` (arm along `+x` at
`θ = 0`, joint 2 at `(l₁, 0, 0)`, `l₂` the distance from joint 2 to the end effector); the kinematic
arm `planarTwoLink` of Chapter 3 (along `+y`) is a different convention and is not used.

**Linearization and the eigenvalue criterion (Theorem 4.6, pp. 184–185; commit `a6e35d6`).** The uniform
linearization (4.39) is `Stability.IsUniformLinearization f A` with `A : ℝ → (E →L[ℝ] E)`, time
first: for every `γ > 0` some `r > 0` gives `‖f(t, x) − A(t)x‖ ≤ γ‖x‖` for all `t ≥ 0` and
`‖x‖ ≤ r`; it implies `f(t, 0) = 0` for `t ≥ 0`, MLS's assumption on (4.37). MLS's
`∂f/∂x|_{x=0}` is the Fréchet derivative at `0` (`HasFDerivAt`); for an autonomous `F` with
`F(0) = 0` this is exactly (4.39) (`isUniformLinearization_of_hasFDerivAt`). The linear map of a
real `n × n` matrix is `LinearMap.toContinuousLinearMap (Matrix.toLin' A)`, `x ↦ A x` on
`Fin n → ℝ`, with the operator norm of the sup norm; on matrices the same norm is Mathlib's
`Matrix.Norms.Operator` (largest row sum of absolute values; `Matrix.linfty_opNorm_eq_opNorm`),
opened only where needed. "All eigenvalues in the open left half plane" is `Control.IsHurwitz A`:
`Re μ < 0` whenever `A v = μ v` for some `v ∈ ℂⁿ`, `v ≠ 0`, with `A` acting entrywise through
`ℝ → ℂ` (equivalently, on the complex spectrum); the name is the control-text one, not MLS's. The
exponential is `NormedSpace.exp`; a matrix statement elaborates `exp` with the plain product
topology and the normed lemmas meet it by definitional unfolding (`exact`), not by `rw`. Theorem
4.6 is formalized on `ℝⁿ`, with the conclusion exponential stability (Definition 4.3), from which
the printed local uniform asymptotic stability follows: for a constant linearization `A(t) ≡ L`
(commit `a6e35d6`) and for a time-varying `A(t)` (commit `88a6f54`). Other finite-dimensional
state spaces, such as `ℝ × ℝ`, are reached by `ExponentiallyStable.of_continuousLinearEquiv`
(constants change by `‖e‖‖e⁻¹‖`). No continuity of `f`, no Lipschitz condition (p. 179) and no
existence of solutions is assumed. The Lyapunov function of the proof is `xᵀPx` with `P` twice the
finite-horizon Gramian `∫₀^T exp(sL)ᵀ exp(sL) ds` in the Euclidean dot product, compared with the
sup norm through `‖x‖² ≤ x ⬝ x ≤ n‖x‖²` and `QuadraticBounds`.

**Time-varying linearization (commit `88a6f54`).** `A : ℝ → (ℝⁿ →L[ℝ] ℝⁿ)` is "bounded" when `‖A(t)‖ ≤ M` for `t
≥ 0` (operator norm of the sup norm), and is in addition assumed continuous on `[0, ∞)`, a
hypothesis MLS does not state (its p. 179 conditions allow piecewise continuity in `t`; the
library's solutions need a derivative at every `t > t₀`). A state-transition matrix is a family of
continuous linear maps `Φ(t, s) : E →L[ℝ] E` with `IsStateTransition A Φ`: `Φ(s, s) = 1`, `Φ(t,
s)Φ(s, r) = Φ(t, r)` and `∂Φ(t, s)/∂t = A(t)Φ(t, s)` (derivative within `[0, ∞)`), for `t, s, r ≥
0`; `Φ(t, s)` maps the state at time `s` to the state at time `t`, forward or backward, and `t ↦
Φ(t, t₀)z₀` is the solution from `(t₀, z₀)`. It exists when `A` is continuous and bounded on `[0,
∞)` and is unique; for constant `A ≡ L` it is `exp((t − s)L)`. The exponential bound is written
`‖Φ(t, s)‖ ≤ C e^{−α(t − s)}` for `0 ≤ s ≤ t`. The Lyapunov function of the proof is the Gramian
`V(t, x) = ∫_t^{t+T} ‖Φ(s, t)x‖₂² ds` in the Euclidean dot product with `T = 1 + log(2nC'² +
1)/(2α)` (the horizon of the constant case, `C' = max(C, 0)`). For `A` with one-sided limits at every point (MLS's piecewise continuity) a state-transition matrix exists only if `A` is continuous on `[0, ∞)`, because `∂Φ(t, s)/∂t = A(t)Φ(t, s)` is asked at every time; Carathéodory solutions (derivatives off the jump times) are not adopted, so Theorem 4.6 for `A` with jumps is not formalized (commit `0867eac`).

**Differentiable flows (Theorem 4.5, the fourth bound).** For a time-varying field `f(t, x)` (time
first) a differentiable flow is `IsDifferentiableFlow f Df φ D`: `Df t y` is the Fréchet derivative of
`f(t, ·)` at `y` for `t ≥ 0`; `φ t s x` is the state at time `t` of the solution starting from `x` at
time `s` (MLS's `s(t, x, s)`), defined and used for `0 ≤ s ≤ t`; every solution from `s ≥ 0` is
`t ↦ φ t s (x s)`; `(t, s, x) ↦ φ t s x` is continuous on `0 ≤ s ≤ t`; `D t s x` is the Fréchet
derivative of `φ t s` at `x`, `D s s x = 1`, and `∂D/∂t = Df(t, φ t s x) D` within `[s, ∞)` (the
variational equation). It is a hypothesis structure, like `HasFlow` and `IsStateTransition`:
differentiable dependence on initial conditions is not in the pinned Mathlib. A state-transition
matrix gives one with `φ t s x = Φ(t, s)x`, `D = Φ`. The converse function is
`V(t, x) = ∫₀^T ‖φ(t + u, t, x)‖₂² du` with the Euclidean norm (so that `V` is differentiable), compared
with the sup norm through `‖x‖² ≤ x ⬝ x ≤ n‖x‖²`; the four bounds are stated for `t ≥ 0` and
`‖x‖ ≤ ε/2`, half the `ε` of Definition 4.3, so that `∂V/∂x` is taken inside the ball where the
exponential estimate holds; `‖∂V/∂x‖` is the operator norm for the sup norm.

**Differentiable dependence on initial conditions.** A differentiable flow is constructed
(`exists_isDifferentiableFlow`) for a field `f(t, x)` on a real Banach space that is continuous
in `t ≥ 0` for every `x` and has a Fréchet derivative `Df(t, y)` in `y`, continuous in `(t, y)`
and bounded in operator norm by `K` on `[0, ∞) × E`. These replace MLS's "Lipschitz in `x`,
uniformly in `t`, and piecewise continuous in `t`" (p. 179): a bounded derivative is the same as
the uniform Lipschitz bound for a differentiable field, continuity in `t` gives the derivative
at every time that `IsSolution` asks, and a continuous derivative is the standard hypothesis of
differentiable dependence. The field is extended to negative times by its value at `0`; the
solutions are global (forward and backward) solutions of the extended field, from Picard–Lindelöf
on intervals of a length fixed by `K` glued by uniqueness; `D(·, s, x)` is the state-transition
matrix of `A(τ) = Df(τ, φ(τ, s, x))`. For every such flow `(t, x) ↦ D(t, s, x)` is continuous on
`[s, ∞) × E`, so `φ(t, s, ·)` is strictly differentiable; continuity of `D` in the initial time
`s` and higher derivatives are not proved. For `ℝⁿ` the converse of Theorem 4.5
with all four bounds then holds under these hypotheses with no flow hypothesis
(`exponentiallyStable_iff_exists_lyapunov_of_fderiv`). A field whose derivative is bounded only
near the origin is not covered.

**Robots under PD control (Proposition 4.9, p. 193, for every robot, p. 301).** For a robot
`Control.RobotSystem p`, PD with compensation of `N` is `F = N(x, ẋ) − K_vẋ − K_p(x − x_d)` for a
constant `x_d`; its closed loop is (4.52). A robot carries no regularity: `M` continuous and
`Control.DifferentiableAlongMotions M` (the entries of `s ↦ M(x(s))` have derivatives along every
motion) are hypotheses, with the skew property `HasSkewProperty`, `M(x)` positive definite, and for
convergence `λ‖v‖² ≤ vᵀM(x)v` and a solution flow (`HasFlow`) of the closed loop. The energy identity
`V̇ = −ẋᵀK_vẋ` is also stated along a motion for matrix curves `M(s)`, `C(s)` with `M(t)` symmetric and
`Ṁ − 2C` skew at `t` (`Control.hasDerivAt_pdEnergy_along`), the form used when the matrices depend on
coordinates that are not part of the state (MLS p. 301).

**Workspace PD law (p. 198).** The law is `τ = JᵀF`, `F = Ñ(θ, θ̇) − K_vẋ − K_p(x − x_d)`, `x = f(θ)`,
`ẋ = J(θ)θ̇`, a constant workspace set point `x_d` (`workspacePDTorque`); where `J` is invertible it is
`τ = N − JᵀK_vJθ̇ − JᵀK_p(f(θ) − x_d)`. Its workspace energy `½ẋᵀM̃ẋ + ½(x − x_d)ᵀK_p(x − x_d)` has
derivative `−ẋᵀK_vẋ` along every motion at every time where `J` is invertible. MLS's "smooth and
invertible" (p. 196) is read, for the stability statements, as `f` of class `C²` with a
differentiable two-sided inverse `g` (then `J` is invertible everywhere); the workspace system is then
the robot `workspaceRobot f g` in `x`: `M(x) = M̃(g(x))`, `C(x, ẋ) = C̃(g(x), J⁻¹ẋ)`,
`N(x, ẋ) = Ñ(g(x), J⁻¹ẋ)`, `J = J(g(x))`. Joint solutions under `τ = JᵀF` map to workspace solutions
under `F` by `(θ, θ̇) ↦ (f(θ), Jθ̇)` and back by `(x, ẋ) ↦ (g(x), J⁻¹ẋ)`, so a flow of the joint closed
loop gives one of the workspace closed loop; the stability statements take the joint flow as the
hypothesis. The tracking version (Exercise 9, p. 209) is the paragraph "Workspace augmented PD" below. The planar instance uses the absolute link angles
`x = (θ₁, θ₁ + θ₂)`; the xy map of Example 4.8 has no global inverse.

**Proposition 4.10's `ε` (p. 195).** For the planar two-link arm no single `ε > 0` makes the corrected
`V̇` negative definite on the whole state space: every `ε` leaves a state, of size of order `1/ε`, where
it is positive (an instance). On a bounded set of initial errors one `ε` suffices, which is the local
reading of MLS's argument through Theorem 4.5 (p. 183), so the smallness of `ε` depends on the region
of initial errors; for a constant inertia with a bounded skew `C` one `ε` serves every initial error.
The formal conclusion stays semiglobal, global for constant inertia with a bounded skew `C`.

**Robots under augmented PD (Proposition 4.10, pp. 194–195, for every robot, p. 301; commit
`1b9a28e`).** The law (4.53) for a robot is `F = M(x)ẍ_d + C(x, ẋ)ẋ_d + N(x, ẋ) − K_vė − K_pe`; the
skewed energy is MLS's `V`; along motions `Ṁ = C + Cᵀ` (from the skew property and the symmetry of
`M`), so the rate is written without `Ṁ`: `V̇ = −ėᵀK_vė + εėᵀMė − εeᵀK_pe + ε(−eᵀK_vė + ėᵀC(x, ẋ)e)`.
Hypotheses: those of Proposition 4.9 for robots (`M(x)` positive definite, continuous, differentiable
along motions, the skew property), `M` uniformly positive definite and bounded,
`|vᵀC(x, u)w| ≤ δ‖u‖‖v‖‖w‖`, `ẋ_d` bounded for `t ≥ 0`; the conclusion is semiglobal as for the
manipulator, and global when `|vᵀC(x, u)w| ≤ c‖v‖‖w‖` uniformly, a hypothesis which, with the skew property and `Ṁ = C + Cᵀ`, forces `M` constant and `C` skew-symmetric, so the global case is exactly constant inertia with a bounded skew `C`.

**Workspace augmented PD (Exercise 9, p. 209; commit `1b9a28e`).** `τ = JᵀF` with `F` the augmented PD
law of the workspace robot `workspaceRobot f g` (desired workspace trajectory `x_d`); the tracking error
is the workspace error `(f(θ) − x_d, Jθ̇ − ẋ_d)` of the joint solution; hypotheses: `f` of class `C²`
with a differentiable inverse `g`, `M̃` uniformly positive definite and bounded, the workspace robot's
`C̃(g(x), J⁻¹u)` bounded by `δ‖u‖`, `ẋ_d` bounded.

## Grasp and contact conventions

Recorded 2026-10-11 14:31 UTC with commit `cc0fd5f`. Source: MLS Chapter 5 §§2–3, printed pp. 214–228,
read as text, with the formula pages inspected as renders.

**Frames.** The object frame `O` sits at the object's center of mass (p214); nothing in the
library uses that choice. The contact frame `Cᵢ` has its origin at the contact point and its
`z`-axis along the *inward* surface normal (pp214–215); in the planar Example 5.3 the contact
`y`-axis is the inward normal (p222). `g_{ocᵢ} = (p_{cᵢ}, R_{cᵢ})` takes contact coordinates to
object coordinates (p215), the library's `g_AB` direction. The contact location is fixed on the
object (p214). Frames are data: no type checks that a frame's `z`-axis is an inward normal. MLS
§6 changes convention: the contact frame along a surface curve is the normalized Gauss frame
`[c_u/‖c_u‖, c_v/‖c_v‖, n]`, `n = c_u × c_v/‖c_u × c_v‖` (p245, eq. (5.22); p246, footnote 2:
"This is different from our previous convention, where we choose the z-axis along the inward
pointing normal"). Whether `n` points outward depends on the chart's orientation; the library keeps the book's `n` and states outwardness as a hypothesis, and relates the two frames by a fixed rotation (subsection "Rolling contact (§6)" below).

**Contact wrenches and the transfer.** A contact wrench `F_c = (f, τ)` acts at the contact origin
and is written in the contact frame, force first, as `Wrench` (MLS p61). It is carried to the
object frame by `Wrench.transform g_{oc}`, which the library identifies with `Ad_{g_{oc}⁻¹}ᵀ`
(p218 and eqs. (2.65)–(2.67)). Contact wrenches are summed only after this transfer
(`Wrench.net`, p219).

**Coefficients and cones (design question Q1).** A friction cone lives in the space of contact
force *coefficients* (`ℝ^m`, as in the book), not in the wrench space; the cone of wrenches a
contact can apply is the image `B_c(FC_c)` (`ContactModel.wrenchCone`), and that of the grasp is
`G(FC)`. Coefficients are `Fin m → ℝ` with the product topology (the Euclidean topology). Lean
coefficient `j` is the book's `f_{j+1}`; the normal force of a spatial contact is Lean `f 2`, of a
planar contact Lean `f 1`.

**Friction cone carrier (Q3).** `FrictionCone E` bundles a Mathlib `ConvexCone ℝ E` (Definition
5.1, property 2: closure under positive scaling and addition, which with `α, β > 0` is the printed
property) with closedness and nonempty interior (property 1). A friction cone contains `0` (not
stated by MLS; it follows). The printed cones are convex cones for every coefficient; they are
friction cones under the book's `μ > 0`, `γ > 0`.

**Grasp map (Q2).** A grasp map is a real linear map from contact force coefficients to object
wrenches; for a contact grasp the coefficient space is `(i : ι) → Fin (m i) → ℝ` (the book's
`f_c = (f_{c₁}, …, f_{c_k})`), and the friction cone is the product cone. The book's `p × m`
matrix is `ContactGrasp.matrix e` in wrench coordinates `e` (for spatial grasps
`Wrench.coordinatesEquiv`, six rows force first), with columns indexed by `Σ i, Fin (m i)` in the
stacked order; printed matrices with `Fin m` columns are compared through the stacked vector
`![f 0 0, f 0 1, …]` in the printed order.

**Planar grasps (Q4).** Planar wrenches are coordinate vectors `Fin 3 → ℝ` in the order
`(f_x, f_y, τ)`, `τ` the moment about the normal to the plane (p222). A planar contact frame is
`(R, p)` with `R ∈ SO(2)` (Mathlib's `specialOrthogonalGroup (Fin 2) ℝ`) and `p ∈ ℝ²`; its wrench
transfer is the printed `[[R, 0], [[-p_y, p_x]R, 1]]`. Embedding `R` as `[[R, 0], [0, 1]] ∈ SO(3)`,
`p` as `(p_x, p_y, 0)` and a planar wrench as force `(f_x, f_y, 0)` and moment `(0, 0, τ)`, the
planar rule is the spatial rule (2.66) (`Planar.transform_embedWrench`).

**Force-closure (Q8).** `Grasp.ForceClosure G FC` is Definition 5.2 with unbounded contact force
magnitudes; it presumes the contacts are maintained and rigid (p214). It says nothing about
bounded actuators, contact persistence, slip under dynamics or a physical hand. Every
force-closure docstring repeats this caveat.

**Internal forces.** Definition 5.3 (p223) is followed: internal `N(G) ∩ FC`, strictly internal
`N(G) ∩ int(FC)`. Table 5.4 (p239) calls the latter "internal forces"; the library does not use
the table's wording.

**Positive spans (Q7).** "Positively spans" is defined as printed (p225), with strictly positive
coefficients; `Grasp.positivelySpans_iff_nonneg` proves it equivalent to spanning with
nonnegative coefficients, the form used in proofs.

**Q5 (settled with commit `5e09b00`).** The §6 normal is the book's `n = c_u × c_v/‖c_u × c_v‖`, outwardness is an explicit hypothesis, and the §2 contact frame is the Gauss frame turned by `π` about its `x`-axis (subsection "Rolling contact (§6)"). Q6, the strictness of the antipodal conditions of Theorem 5.6, is settled with commit `e736100` (below).

### Hands, finger kinematics and manipulability

Recorded 2026-10-11 15:46 UTC with commit `be8093a`. Source: MLS Chapter 5 §5, printed pp. 234–242, read
as text with the formula pages inspected as renders.

**Hand frames.** The palm frame `P` is fixed and the object configuration is `x_o = g_{po}` (p215,
p237). Finger `i` is a serial chain (`SerialChain`) from its base frame `Sᵢ`, fixed in the palm, to
its fingertip frame `Fᵢ`, which moves with the fingertip: its joint twists are written in `Sᵢ` at
the reference configuration and `g_{sᵢfᵢ}(θ) = fk θ` (MLS Chapter 3, product of exponentials). The
library stores the base pose `g_{psᵢ}` (`HandGrasp.base`); MLS writes `g_{sᵢp} = g_{psᵢ}⁻¹`. The
contact frame `Cᵢ` is fixed on the object (`g_{ocᵢ}` constant, the fixed-contact assumption of p234)
and `g_{sᵢcᵢ} = g_{sᵢp} g_{po} g_{ocᵢ}` (`HandGrasp.contactFrame`, pp236, 240). `Fᵢ` and `Cᵢ` are both
"located at the contact point" (p234), but no result uses that they coincide.

**Velocities.** As MLS does from p235 on, all velocities are body velocities. `V^b_{fᵢcᵢ}` is the
body velocity of `g_{fᵢcᵢ} = g_{pfᵢ}⁻¹ g_{pcᵢ}`, with `g_{pfᵢ} = g_{psᵢ} g_{sᵢfᵢ}(θᵢ)` and
`g_{pcᵢ} = g_{po} g_{ocᵢ}` (`HandGrasp.fingertipContact`); `V^b_{po}` is the body velocity of the object
relative to the palm. The relations (5.8), (5.10)–(5.12) are proved along trajectories with actual
derivatives (`bodyVelocity_fingertipContact`); the contact constraint (5.9), `B_{cᵢ}ᵀ V^b_{fᵢcᵢ} = 0`,
is the hypothesis of a maintained contact (`ContactConstraint`), equivalent to (5.13). `B_cᵀ` and
`Gᵀ` act on twists through the pairing `f·v + τ·ω` of MLS p61 (`ContactModel.constraint`,
`SpatialGrasp.graspTranspose`): `(Gᵀ V)·f_c = (G f_c)·V`; in six coordinates, wrench rows force
first against twist rows linear first, they are matrix transposes.

**Hand Jacobian.** Joint rates are `(i : ι) → Fin (n i) → ℝ` (the book's stacked `θ ∈ ℝⁿ`), contact
velocities and forces `(i : ι) → Fin (m i) → ℝ`; matrices use the stacked indices
`Σ i, Fin (n i)` and `Σ i, Fin (m i)` of `ContactGrasp.stack`. `J_h(θ, x_o)` is block diagonal by
construction, with blocks `B_{cᵢ}ᵀ Ad⁻¹_{g_{sᵢcᵢ}} J^s_{sᵢfᵢ}(θ_{fᵢ})` and `J^s` the library's spatial
Jacobian (3.54) in the finger base frame. The display defining `J_h` on p236 carries no printed
number (the label "(5.14)" is overprinted on "(5.13)" in the next sentence); the library calls it
(5.14).

**Joint torques (5.16).** MLS obtains `τ = J_hᵀ f_c` "by equating the work done by the joints and
contacts" (p238). The library defines `τ` as the transpose itself (for a hand, `handTorque`; for a
general multifingered grasp, the linear form `θ̇ ↦ f_c·(J_h θ̇)` on joint rates) and proves only the
instantaneous power identity and its uniqueness step; the work premise, as for (3.59)–(3.60), is
not formalized. `f_c ∈ FC` is not imposed by the definition.

**Multifingered grasps and manipulability.** Definition 5.4 is bundled at one configuration as a
hand Jacobian from any real joint-rate space and a spatial grasp (`MultifingeredGrasp`), so the
object side is `Wrench`/`Twist` (`p = 6`). Manipulability (Definition 5.5) quantifies over every
object twist and unbounded joint rates at maintained contacts; like force-closure it says nothing
about actuator limits, contact persistence or a physical hand. Table 5.4's "internal forces" are
Definition 5.3's strictly internal forces; its "structural forces" row (`G⁺`) is not used;
"structurally dependent forces" are contact forces with `J_hᵀ f_c = 0` (p239).

**Summary item 6 (p257).** For a general multifingered grasp, manipulable and surjective `J_h` are
not equivalent under force-closure (`Examples.summaryItem6_counterexample`); for hands with onto
contact constraint maps (every Table 5.2 model) they are equivalent without force-closure
(`HandGrasp.isManipulable_iff_surjective`). Statements about "the" hand Jacobian use the latter.

### Grasp planning and antipodal grasps

Recorded 2026-10-13 with commit `e736100`.
Source: MLS Chapter 5 §4, printed pp. 229–234, and Exercises 5, 7, 8 (pp. 260–261), read as
renders and text extracts.

**2-D cross product and `n^⊥`.** `a ⊗ b = det[a b] = a_x b_y - a_y b_x` (`Grasp.cross2`, p. 232);
`n^⊥ = (-n_y, n_x)` (`Grasp.perp2`), the unique unit vector with `n · n^⊥ = 0` and
`n ⊗ n^⊥ = +1` for a unit `n` (`perp2_unique`). Not to be confused with `Vec3.perp`, the projection
onto a plane.

**Planar contact axes.** For a planar frame `R ∈ SO(2)` (p. 222): contact `x`-axis
`t = R e_x` (`contactTangent`), inward normal `n = R e_y` (`contactNormal`), `t ⊗ n = det R = 1`
and `n^⊥ = -t`. The planar wrench of a force `F` at `p` is `(F_x, F_y, p ⊗ F)` (`planarWrench`).

**Conditions A–D and Q6.** A–D are taken as printed, strict, one `μ`: A ∧ B at contact 1 for
`p₂ - p₁`, C ∧ D at contact 2 for `p₁ - p₂` (`InsideFrictionCone`, `AntipodalConditions`). "The line
lies inside the friction cone" means the open cone: A ∧ B ⇔ `|t · d| < μ (n · d)` ⇔ `Rᵀ d` in the
interior of the cone of p. 222 ⇔ `d` in the interior of the contact's cone in object coordinates.
The boundary (any of A–D at equality) is never force-closure, and the closed reading is false on an
explicit instance.

**Orientation hypothesis of Theorem 5.6 (not stated by MLS).** The "only if" direction needs the
inward normals to face each other, `n₁ · (p₂ - p₁) ≥ 0` and `n₂ · (p₁ - p₂) ≥ 0`
(`NormalsFaceEachOther`; one of the two suffices), which holds on a convex object. Without it
force-closure is equivalent to A–D or A–D with the connecting line reversed at both contacts; the
exchanged rectangle of Example 5.3 (an internal grasp) is force-closure and fails A–D.

**Contact bounds.** Theorems 5.4 and 5.5 carry the added hypothesis `p ≥ 1`. Families may repeat
vectors; bounds count members. `ℝ^p` is any finite-dimensional real vector space (5.4) or normed
space (5.5); `co` is `convexHull ℝ`, `int` is `interior`.

**Surfaces and `Λ(Σ)`.** A "surface" is a set of (contact point, normal) pairs in object
coordinates; no boundary `∂O` is modeled and nothing checks unit length or inwardness. Planar
`Λ(Σ)` uses `(n_x, n_y, p ⊗ n)`; spatial `Λ(Σ)` uses the six coordinates of `(n; p × n)`, force
first, with the product topology. Exceptional: `convexHull ℝ Λ(Σ) ∉ nhds 0`. A planar frictionless
grasp of contacts on a surface is the matrix of its columns (Example 5.4's form); a spatial one is
`ContactGrasp.spatial` of frictionless contacts with translation `pᵢ` and third axis `nᵢ`.

**Theorem 5.7.** "The line lies inside the friction cone" at a soft-finger contact means the
direction to the other contact, in that contact's frame (`contactDirection`), satisfies the open
Coulomb inequality `√(x₁² + x₂²) < μ x₃`; the torsional part of the cone (5.4) plays no role in the
hypothesis. The "if" direction holds in the library's model; the printed "only if" fails there at
every `γ > 0` (for `μ = 1`, `Examples.softAntipodal_onlyIf_fails`). What holds: a force-closure
grasp carries opposite forces strictly inside both Coulomb cones whose moment about the line is
balanced by the torsions, `(p₁ − p₀) × F = t₀n₀ + t₁n₁` with `|tᵢ| < γ fᵢ₃` (the torsional form,
no added hypothesis); and when the inward normals `nᵢ = Rᵢe_z` and the line `p₁ − p₀` are
coplanar (some `m ≠ 0` is orthogonal to all three) and the first normal does not point away from
the second contact (`n₀ · (p₁ − p₀) ≥ 0`), force-closure is equivalent to the line lying inside
both open cones, for every `γ > 0`. Both hypotheses are added to the printed statement.

**Figure 5.13.** The book defines no axes; the library uses the triangle `(0, 0)`, `(1, 0)`,
`(1/2, √3/2)`, contacts `(s, 0)` and `(t/2, t√3/2)` measured from the shared vertex.

**Contacts of several point contacts (Exercise 4, pp. 259–260).** A line or plane contact is read
as Coulomb point contacts with friction (eq. (5.3), one `μ > 0`) at finitely many points `qᵢ` of the
contact frame: the endpoints `(∓l, 0, 0)` of a segment along the contact `x`-axis, the corners
`(±a, ±b, 0)` of a rectangle. Coefficient `(i, j)` (index `finProdFinEquiv (i, j)`) is the `j`-th
contact-frame component of the force at `qᵢ`; the friction cone is the product of the Coulomb cones;
wrenches are at the contact origin in the contact frame (p. 218). A Coulomb force applied anywhere
in the segment or rectangle is a sum of corner forces; pressure distributions are not modeled.

**Exercise figures (pp. 259–261).** The figures fix no axes. Exercise 2(a): the triangle of
Figure 5.13 with contacts at the edge midpoints; Exercise 2(b): the midpoints `s = t = 1/2` of the
Figure 5.13 parametrization; Exercise 3(b): contacts at `(0, 0, ∓r)` with the identity and the
rotation by `π` about `x`; Exercise 8(c): the rectangle `[0, 2] × [0, 1]`; Exercise 9: a circle of
radius `r` about the origin, the contact at angle `α` with tangent `(−sin α, cos α)` and inward
normal `(−cos α, −sin α)`. Planar frames follow p. 222 (`y`-axis the inward normal, `t ⊗ n = 1`). Exercise 2(c): the unit sphere with contacts at `(±1, 0, 0)` and `(0, 0, 1)`; Exercise 5(b): the
regular tetrahedron `{x : ⟨vₖ, x⟩ ≥ −1}` with vertices `(1, 1, 1)`, `(1, −1, −1)`, `(−1, 1, −1)`,
`(−1, −1, 1)`, contacts on its faces with the inward face normal `vₖ/√3` as contact `z`-axis
("no vertex contacts" read as no vertex or edge contacts); Exercise 8(a): the trapezoid with
vertices `(0, √3/2)`, `(2, √3/2)`, `(3/2, 0)`, `(1/2, 0)`, leg points parametrized from the top
corners. Exercise 11: the fingertip of Figure 5.17 is horizontal at the foot of the vertical rod
and points along the last link at `θ = 0`, so `g_st(0) = (I, (0, l₁ + l₂ + l₃, l₀))`; the spatial
Jacobian does not depend on it. Exercise 12: "equate the locations" is the zero translation of
`g_{fᵢcᵢ}`, whose derivative gives the translational rows of (5.13).

### Rolling contact (§6)

Recorded 2026-10-16 with commit `5e09b00`. Source: MLS Chapter 5 §6, printed pp. 242–255 and 257,
and Exercises 13, 16 and 17, pp. 262–263, read as renders and text extracts.

**Charts.** A chart is a map `c : (Fin 2 → ℝ) → Vec3`; the coordinates `α = (u, v)` are indexed `0, 1`,
and `c_u`, `c_v` are the derivative `fderiv ℝ c α` applied to `(1, 0)` and `(0, 1)`
(`Surface.partialU`, `partialV`). Hypotheses are explicit per statement; `IsOrthogonalChartOn c U`
bundles an open `U`, twice continuous differentiability on `U` (the book prints "differentiable";
`n_u`, `n_v` and (5.24) use second derivatives), an injective differential (condition 3, p. 243) and
`c_u ⟂ c_v` (p. 244). Condition 2 (homeomorphism) and Theorem 5.9 are not used. `c_uv` is `∂c_u/∂v`,
equal to `∂c_v/∂u` for a twice continuously differentiable chart.

**Normal and orientation (Q5).** The Gauss map is exactly the book's `n = c_u × c_v/‖c_u × c_v‖`
(5.19), with no sign added. Whether `n` points out of a body depends on the chart: for a body
`{x : h x ≤ 0}`, `IsOutwardNormal h c α` says that the directional derivative of `h` at `c(α)` along `n` is positive. The boundary condition `h (c α) = 0` is not part of the predicate, which also holds at points off the body; a statement that places `c(α)` on the boundary must assume it separately. The chart of Example 5.6 has an inward normal (its curvature tensor is `−(1/ρ) I`, against
the printed `(1/ρ) I`), the finger chart of Example 5.7 (the mirror image in `y`) an outward one with
`K_f = (1/ρ) I`. With an outward normal a convex surface has positive curvature. The kinematic theorems
(Lemma 5.10, Theorem 5.11) need no orientation hypothesis; the physical reading of two bodies touching
from outside needs both normals outward.

**Metric, curvature and torsion.** `M_p = diag(‖c_u‖, ‖c_v‖)` is the printed orthogonal-chart form.
`K_p` is defined by the entries of (5.21) and equals `M_p⁻ᵀ II_p M_p⁻¹` and (5.23). `T_p` is defined
by the first expression of (5.24) and read as a row: `T M α̇ = T ⬝ᵥ (M α̇)`. The book's "If a surface
is flat, then `T_p = 0`" holds for affine charts; a polar chart of a plane has `T_p ≠ 0`.

**Frames.** The normalized Gauss frame `[x y n]` is a rotation for an orthogonal chart with nonzero
partials; `Surface.gaussFrame c α` is that rotation there and the identity elsewhere, so that a frame
curve is defined along every coordinate curve. The contact frame is `g_oc(α) = (c(α), [x y n])`, the frame of the proof of Lemma 5.10, and the frame of (5.42) for a chart whose Gauss normal is outward; for an inward one, (5.42)'s matrix with the outward normal is `[x y −n]`, of determinant `−1`.

**Contact coordinates and `ψ`.** `η = (α_f, α_o, ψ)`. `R_ψ = [[cos ψ, −sin ψ], [−sin ψ, −cos ψ]]` as
printed on p. 250 (a reflection: `R_ψᵀ = R_ψ`, `R_ψ² = I`, `det R_ψ = −1`); `K̃_o = R_ψ K_o R_ψ`. The
contact rotation is `R_{c_o c_f} = diag(R_ψ, −1)`: the printed (5.34) has `+1`, which gives
determinant `−1`; with `−1` the normals are opposed and (5.34)'s `ω_{c_o c_f} = (0, 0, ψ̇)` holds. The
relative pose (not printed) is `g_of(η) = g_{oc_o}(α_o) · (0, diag(R_ψ, −1)) · g_{fc_f}(α_f)⁻¹`. Then
`x_f ↦ cos ψ x_o − sin ψ y_o`: `ψ` is the right-handed angle from `x_o` to `x_f` about the finger's
outward normal `−n_o`. The prose of p. 248 ("a rotation ... around the outward normal of `S_o`"),
read with the right-hand rule about `n_o`, gives the opposite sense; the library follows the matrix. A reading of Figure 5.21 (p. 249), Plausible and not formalized (the arc carries no sign): with the drawn triad of `O` right-handed, `n_o` to the right, `∂c_o/∂u_o` toward the reader and `∂c_f/∂u_f` down, the arc from `∂c_o/∂u_o` to `∂c_f/∂u_f` is a right-handed rotation by `+90°` about `n_o`, which is `ψ = −90°` in the library's sense; on this reading the figure also shows the prose sense.

**Montana's equations.** Theorem 5.11 is stated as the library states (5.8)–(5.13): along a pose curve
`g` that agrees near `t` with `g_of(η(s))`, `η` with actual derivatives at `t`, for every derivative of
`g`, the relative velocity is `V_{l_o l_f} = Ad⁻¹_{g_{fc_f}(α_f(t))} V^b_of` (the local frame frozen at
time `t`; (5.27) with the finger's contact point `c_f(α_f)`, not the printed `p̂_o`). Then (5.37) holds,
`v_z = 0` included, as a theorem; (5.28) follows when `K_f + K̃_o` is invertible (the book's p. 251
hypothesis; `M_f`, `M_o` are invertible for orthogonal charts). Pure rolling is `v_x = v_y = 0`,
`ω_z = 0` and pure sliding `ω = 0` (p. 249).

**Bridge to the contact frames of §2.** The §2 contact frame (`z` along the inward normal, p. 214) is
`Rolling.inwardContactFrame c α = g_oc(α) · (0, diag(1, −1, −1))`: same origin, `x` kept, `y ↦ −y`,
`z = −n`, pointing into the body when `n` is outward. The finger's Gauss frame at the contact is
`inwardContactFrame c_o α_o · (0, R_z(ψ))`. The §2 contact models (`ContactModel`, friction cones,
`B_c`) apply unchanged in `inwardContactFrame`; the book's (5.42), with `z` along the outward normal,
would need `B_c` rewritten, which it does not do.

**Exercise 17 (planar contact).** Points and vectors of the plane are `Fin 2 → ℝ`; `g_of = (p, R)` with
`R ∈ SO(2)`. A chart has unit tangent `t = c'`, normal `n = J t` with `J` the rotation by `+π/2`, and
curvature `K` defined by `n' = K t` (the planar form of (5.23)). The curves are in contact when
`c_o(s_o) = p + R c_f(s_f)` and `n_o = −R n_f`.

**Contact kinematics `A(η)` (5.40).** The contact coordinates are `η = (α_f, α_o, ψ) ∈ ℝ² × ℝ² × ℝ`
(`Rolling.ContactCoords`), stacked in `ℝ⁵` in the order `(u_f, v_f, u_o, v_o, ψ)` of (5.39). `A(η)`
is the linear map from `V^b_of` to the rates given by the first three lines of (5.28) at `V_{l_o
l_f} = Ad⁻¹_{g_{f c_f}(α_f)} V^b_of`; its matrix has the six twist coordinates `(v, ω)` as columns.
(5.28) is `η̇ = A(η) V^b_of` together with `v_z = 0`.

**Hands with rolling contacts.** A `RollingHand` holds, per contact, the contact model, the finger,
the finger base, a chart of the fingertip surface in the fingertip frame (the tool frame of the
finger chain) and a chart of the object surface in `O`; the contact coordinates are arguments. The
contact frame of contact `i` at `ηᵢ` is the contact frame of §2 at the object's contact point,
`inwardContactFrame c_{oᵢ} α_{oᵢ}` (`z` along `−n_{oᵢ}`), not the Gauss frame of (5.42): the two
give the same velocity constraints for the models of Table 5.2, and the §2 frame keeps the normal
force of the friction cones pointing into the object. At fixed `η` a rolling hand is the
fixed-contact hand with frames `g_{ocᵢ}(ηᵢ)`; a fixed-contact hand is the rolling hand with the
tangent planes of its contact frames as object charts (`c(α) = p + R(α₀, −α₁, 0)`) at `α_o = 0`.

**The contact constraint for rolling contacts.** The first line of (5.40) is derived from (5.9) with
the contact frame frozen at the contact coordinates of the instant, `g_{fᵢcᵢ}(s) = g_{pfᵢ}(s)⁻¹
g_{po}(s) g_{ocᵢ}(ηᵢ(t))`. At a contact pose the frozen relative velocity is `−Ad_{(0, R_z(ψ))}
V_{l_o l_f}`, so (5.9) is `v_z = 0` for a frictionless contact, no sliding for a point contact with
friction and pure rolling for a soft finger. The literal reading of p. 254, a contact frame moving
with the contact together with `B_{cᵢ}ᵀ V^b_{ocᵢ} = 0`, forces `α̇_o = 0` for point contacts with
friction and soft fingers and is not used.

**Contact set and Proposition 5.12.** For two chart patches, `W` is the set of relative poses that
bring a point of the finger patch onto a point of the object patch with opposed Gauss normals; it is
the image of `η ↦ g_of(η)`. A pose is read in `ℝ^{3×3} × ℝ³` (rotation matrix, translation;
`Rolling.poseCoords`), and smoothness on `SE(3)` means smoothness of a map defined on a
neighbourhood in that space. Smoothness classes are Mathlib's, `n = ∞` for smooth charts and `n = ω` for analytic ones: charts of class `C^{n+1}` give an inverse `Ψ` that is `C^n` at the contact pose `g_of(η₀)` and, for `n ≠ ∞`, at every contact pose `g_of(η)` with `η` near `η₀` (commit `c8e2ef7`). For `n = ∞` only the statement at `g_of(η₀)` is made: `C^∞` at one point gives each finite order on a neighbourhood that may shrink as the order grows.

**Surfaces of revolution (Exercises 14–15).** The chart `(r(u) cos v, r(u) sin v, z(u))` has `n =
(−z' cos v, −z' sin v, r')/√(r'² + z'²)`; the direction in which the profile is traversed sets the
orientation, and every instance is traversed so that `n` is outward: the ellipsoid of revolution `(a
cos u, −c sin u)`, the paraboloid `(u, −u²/(2a))` (the solid below `z = −(x² + y²)/(2a)`), the torus
`(R + a cos u, −a sin u)`. Exercise 15 is formalized for an ellipsoid with two equal axes, with the
contact point `(−a, 0, 0)` at `(u, v) = (0, π)` and the object charted as in Example 5.7.

**Exercise 17 for regular charts.** A planar chart of speed `σ` has `c' = σ t`, `n = J t` and
curvature `K` with respect to arc length, `n' = σ K t`; with `σ ≡ 1` this is Exercise 17(a). The
elliptical finger of 17(b) is `(−a sin φ, −b cos φ)`, traversed clockwise from its lowest point so
that `n` is outward; it turns by `R(θ) = [[cos θ, −sin θ], [sin θ, cos θ]]`, and it rolls when its
material point at the contact has zero velocity, `Ṙ c_f + ṗ = 0`.

**Smooth contact coordinates in (5.41).** The contact coordinates of finger `i` are read from its
relative pose `g_{ofᵢ} = x_o⁻¹ g_{psᵢ} g_{sᵢfᵢ}(θᵢ)` by the readout `Ψᵢ` of Proposition 5.12. The book's
"smooth" is read as `C¹` for the readouts and for `θ ↦ η(θ, x_o)`, the order that the `C²` charts of
`IsOrthogonalChartOn` give, and only at joint vectors that put the fingers at contact poses of the
chosen `η₀`. Smoothness in the object pose `x_o ∈ SE(3)` is smoothness along every smooth family of
object poses, read in pose coordinates.

**The three-axis ellipsoid (Exercises 14–15).** For semi-axes `a > b > c > 0` the chart is
`c(s, t) = ((a/k) cos s √(a² − ν), b sin s cos t, (c/k) sin t √(μ − c²))` with `k = √(a² − c²)`,
`μ = b² + (a² − b²) sin² s` and `ν = c² + (b² − c²) sin² t`: the confocal coordinates `μ`, `ν` (the
roots other than `0` of `x²/(a² − λ) + y²/(b² − λ) + z²/(c² − λ) = 1`) reparametrized so that the
chart is smooth through the vertices `(±a, 0, 0)`. It is orthogonal on all of `ℝ²` and regular exactly
where `sin s ≠ 0` or `cos t ≠ 0` (proved); the excluded parameters map to the points
`(±a √((a² − b²)/(a² − c²)), 0, ±c √((b² − c²)/(a² − c²)))`, the four umbilics (the classical fact, not
proved, since the chart is singular there). The geometric parameters are computed on the patch
`{cos t > 0}`, where the normal (5.19) is outward; that this patch covers, on
`(−π, π] × (−π/2, π/2)`, the ellipsoid without the two arcs of `x²/a² + z²/c² = 1` in the plane `y = 0`
that join the umbilics through `(0, 0, ±c)` is a derivation, not proved. The
contact point of Exercise 15 is the vertex `(−a, 0, 0) = c(π, 0)` on the longest axis, which faces the
object in the figure; the principal axes "of length `a`, `b`, `c`" are read as semi-axes.

**Surfaces given as level sets (Exercise 19).** The exercise is read as follows: for a surface
`{f = 0}` charted by `c` with outward normal and gradient `G` of `f`, the unit normal is `G/‖G‖` and
the curvature tensor (5.21) is the Hessian `DG` on the tangent plane divided by `‖G‖`,
`K_ij = c_iᵀ DG c_j/(‖G‖ ‖c_i‖ ‖c_j‖)`; the metric tensor and the torsion form are those of the chart,
so (5.28) applies unchanged. The test, an ellipsoid rolling on a plane, is Exercise 15(b) for the
three-axis ellipsoid. A chart-free form of (5.28), with the contact point a pair of points of `ℝ³`, is
not formalized.

**The contact set of two bodies and the change of chart.** A body's surface is an atlas: charts
`c i` on domains `U i` indexed by any type, patches allowed to overlap. The contact set `W` is the set
of relative poses that bring a point of some finger patch onto a point of some object patch with
opposite Gauss normals; it depends only on the set of surface points with their unit normals. Where two
orthogonal charts describe the same point with the same normal, their normalized Gauss frames differ
by a rotation `R_z(θ)` about the normal, and the contact coordinates `(α, α_o, ψ)` in the old chart and
`(β, α_o, ψ + θ)` in the new one give the same relative pose: the contact angle shifts by the angle
between the two frames, the configuration does not change.

**Theorem 5.9 and lines of curvature.** Theorem 5.9 is the named statement
`OrthogonalChartStatement` (smooth chart with injective differential, smooth injective
reparametrization onto a neighbourhood). A line of curvature is a coordinate line along which
Rodrigues' formula `n_u = κ c_u` holds; an umbilic of an orthogonal chart is a point where `K` is a
multiple of the identity.

## Constrained dynamics conventions

Recorded 2026-10-13 with commit `d9b95e6`.
Source: MLS Chapter 6, printed pp. 265–284, read as renders and text extracts.
These are conventions of the Lean model; they do not certify a physical constrained system.

**Constraint carrier.** Configurations and velocities are `Fin n → ℝ`; the book's open set `Q` is
all of `ℝⁿ` unless a statement names a set (`IsIntegrableOn`) or a neighborhood. A Pfaffian
constraint is a field `A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ`, satisfied at `(q, v)` when
`A(q) v = 0` (`PfaffianAt`). "Pointwise linearly independent" (p. 267) is
`LinearIndependent ℝ (A q).row`; it is a hypothesis where used, not part of the carrier. A
holonomic constraint `h : ℝⁿ → ℝᵏ` has `∂h/∂q = MapJacobian.jac h`.

**Virtual displacements and d'Alembert's principle.** A virtual displacement at `q` is any `δq` with
`A(q) δq = 0`; a force `F` does no virtual work when `F · δq = 0` for all of them
(`DoesNoVirtualWork`). d'Alembert's principle (pp. 268, 271) is a modeling assumption and is built
into the definitions: the constraint force in (6.4) is `Aᵀλ`, and (6.7)–(6.8) restrict to virtual
displacements. The library proves that the forces doing no virtual work are exactly the `Aᵀλ` (no
rank hypothesis), so the two formulations are equivalent; nothing derives the principle.

**Multipliers.** (6.4) is `Lagrangian.LagrangeEquationsAt` with the force `Υ − Aᵀλ`
(`MultiplierEquationsAt`); `λ ∈ ℝᵏ` is a value at the time `t`, with no regularity in `t`.
Existence of `λ` from (6.7)–(6.8) needs no rank hypothesis; uniqueness holds exactly when the rows of
`A(q(t))` are independent. In (6.7)–(6.8) (`LagrangeDAlembertAt`), as in Lagrange's equations, the
existence of the derivative of `s ↦ ∂L/∂q̇(q(s), q̇(s))` at `t` is part of the predicate. The force
split of Lagrange's equations above is kept: `Υ = F − Nₑ`, `N = ∂V/∂q + Nₑ`.

**The multiplier formula (6.6).** `multiplier A M w a = (A M⁻¹ Aᵀ)⁻¹ ((A M⁻¹) w + a)` with
`Matrix.inv`, `w = F − Cq̇ − N` and `a = Ȧq̇`. Hypotheses where used: `M(q(t))` positive definite;
`Ȧ` an actual entrywise derivative of `s ↦ A(q(s))` at `t`; the constraint on a neighborhood of `t`.

**Relabeling `q = (q₁, q₂)` (p. 272).** A relabeling is an equivalence
`e : Fin r ⊕ Fin k ≃ Fin n`; `q₁ = splitFst e q` (independent coordinates), `q₂ = splitSnd e q`
(the `k` coordinates eliminated by the constraint), `A₁ = colsFst A e`, `A₂ = colsSnd A e`,
`A₂⁻ᵀ = (A₂⁻¹)ᵀ`. "Reordering" means choosing `e`; it exists for independent rows and persists
near a configuration where `A` is continuous.

**The composite hand–object system.** The configuration is `q ∈ Fin N → ℝ` with
`e : Fin p ⊕ Fin n ≃ Fin N`: object coordinates `x = splitFst e q` (`p` of them, the `q₁` of (6.9)),
finger joints `θ = splitSnd e q` (`n`, the `q₂`). MLS's ordering `q = (θ, x)` is
`mlsSplit p n : Fin p ⊕ Fin n ≃ Fin (n + p)` (fingers first). The composite Lagrangian is
`L_f(θ, θ̇) + L_o(x, ẋ)` (6.19). The generalized force is `(τ, 0)` (`handForce`).

**Sign of the grasp constraint.** `A = [J_h  −Gᵀ]` (p. 267, `handPfaffian`), with `J_h ∈ ℝ^{n×n}`
(invertible, so `m = n`) and `G ∈ ℝ^{p×n}`. Then `J_hᵀλ = τ − (M_fθ̈ + C_fθ̇ + N_f)` and
`Gλ = M_oẍ + C_oẋ + N_o`: `λ` is the contact force applied to the object (`Gλ` its net wrench, the
fingers receiving `−J_hᵀλ`), the `f_c` of (5.16) (`τ = J_hᵀ f_c`, p. 238) when
`M_fθ̈ + C_fθ̇ + N_f = 0`. MLS p. 280 prints `A = [−J_h  Gᵀ]`,
which gives `−λ`; the displayed contact-force formula of p. 280 is that of p. 267's sign.

**Object chart (commit `0361f5d`).** `J_h` and `G` may be abstract functions of the
composite configuration `q` (commit `d9b95e6`), or derived from the twist-level grasping constraint
`HandGrasp.GraspingConstraint` (5.15) through a chart `x_o = φ(x)` of the object pose,
`φ : (Fin p → ℝ) → RigidTransform`, with a body-velocity Jacobian `Jφ(x) ∈ ℝ^{6×p}` (rows in twist
order `(v, ω)`): `IsBodyJacobian φ Jφ` is a hypothesis structure stating that along every motion `x`
the pose curve `φ ∘ x` has a derivative and its body velocity `(φ⁻¹φ̇)^∨` is `Jφ(x)ẋ`; column `i` of
`Jφ(x)` is then `(φ⁻¹ ∂φ/∂xᵢ)^∨` (Exercise 4(b), p. 314). Then `J_h(θ, x) = J_h(θ, φ(x))` and
`Gᵀ(θ, x) = Gᵀ Jφ(x)`, i.e. `G(θ, x) = Jφ(x)ᵀ G` (`localGrasp`). On the composite carrier the stacked
contact coefficients `Σ i, Fin (m i)` and joints `Σ i, Fin (n i)` are relabeled to `Fin k` by
equivalences (`chartHandJacobian`, `chartGrasp`, `unstackJoints`); the hand's `J_h` is square when
`Σ m i = Σ n i` (assumption 2 of p. 277). The library's chart instance is the translational chart
`x ↦ (I, x)` with `Jφ = [[I], [0]]`; a chart of `SE(3)` is the pose chart below.

**Effective parameters (6.22).** `effectiveMass Mo Mf J G = M_o + G J⁻ᵀ M_f J⁻¹ Gᵀ` and
`effectiveCoriolis Co Cf Mf J G Bd = C_o + G J⁻ᵀ (C_f J⁻¹ Gᵀ + M_f Bd)`, `J⁻ᵀ = (J⁻¹)ᵀ` with
`Matrix.inv`; the book's `(d/dt)(J_h⁻¹ Gᵀ)` is the explicit argument `Bd`, required to be the actual
entrywise derivative of `s ↦ J_h(s)⁻¹ G(s)ᵀ` wherever (6.21) or Lemma 6.1(2) is used. Hypotheses of
the composite theorems: `M_f`, `M_o` symmetric; `J_h` invertible along the motion near `t`; (6.18)
on a neighborhood of `t`; positive definiteness from `M_o > 0` (any `J_h`, `G`) or from `M_f > 0`,
`J_h` invertible and `G` onto (force-closure); skew symmetry of `Ṁ_o − 2C_o` and `Ṁ_f − 2C_f` as
hypotheses, or from Christoffel matrices of symmetric inertia fields (Lemma 4.2(2)). The
object Coriolis block printed in (6.17) is not used (it is symmetric, O2). Assumptions 1 and 3 of
p. 277 (force-closure and manipulable; contact forces in the friction cone) are not formalized:
the algebra does not use them and the friction-cone condition is a property of the controller.

**Workspace form (6.26).** `G = I` (`p = n`); with `M_o = 0` the effective inertia and Coriolis
matrix are `workspaceM` and `workspaceC` of `Control/WorkspaceControl` (N42).

Recorded 2026-10-14 with commit `0361f5d`.
Source: MLS Chapter 6, printed pp. 274–277, 281–303 and Exercises 2 and 4 (p. 314), read as
renders and text extracts.

**Object dynamics in local coordinates (Exercise 4, (6.17)).** In body coordinates the Newton–Euler
equations read `M V̇ + C(V) V = F` with `M = [[mI, 0], [0, 𝓘]]` (constant) and
`C(V) = [[m ω̂, 0], [0, −(𝓘ω)^]]` (`objectCoriolis`), skew, so `Ṁ − 2C = −2C` is skew; the block
`½(ω̂ᵇ𝓘 − 𝓘ω̂ᵇ)` printed in (6.17) is not used. With gravity, (6.17) is stated with the printed sign,
`Fᵇ = −(Rᵀ(m g⃗), 0)`, the direction of `g⃗` left to the model. In local coordinates
`M̄ = JφᵀMJφ`, `C̄ = JφᵀC(V)Jφ + JφᵀMJ̇φ`, with `J̇φ` the actual derivative of `s ↦ Jφ(x(s))`;
Newton–Euler implies `M̄ẍ + C̄ẋ = JφᵀFᵇ`, and the converse holds for `Jφ` onto.

**The robot interface (§5, p. 303).** A robot is `Control.RobotSystem p`: fields `M(x)`, `C(x, ẋ)`,
`N(x, ẋ)` on `x ∈ ℝᵖ`, no hypotheses inside. Positive definiteness of `M` is a hypothesis where used;
the skew property is `HasSkewProperty` (`Control.SkewAlongMotions M C`: for every motion and every
actual entrywise derivative `Ṁ` of `s ↦ M(x(s))`, `Ṁ − 2C(x, ẋ)` is skew). The first-order system
of a feedback law is `field u` (state `(x, ẋ)`, `Matrix.inv`); the computed torque law is the book's
`F = M(ẍ_d − K_vė − K_pe) + Cẋ + N`, `e = x − x_d` (`computedTorque`; for matrix curves
`computedTorqueAlong`). Proposition 4.8 holds for every robot with `M` positive definite, and along
any motion whose `M(s)` is positive definite, the matrices possibly depending on coordinates outside
the robot's state (p. 301). `ManipulatorModel.toRobotSystem` is the manipulator model of eq. (4.47) as a robot (same
`field` and computed torque, by definition). The hand–object system is a robot on the object
coordinates when the finger fields are written in object coordinates (`handRobot`, the holonomic
case of p. 301); the operations `attach` and `control` are below; inputs and outputs of robots are not modeled as structures.

**The torques (6.36).** `G⁺ = Gᵀ(GGᵀ)⁻¹` is `rightPinv G` (`Matrix.inv`; one definition for `J⁺`,
`P⁺`, `G⁺`), used under `G` onto; `graspTorque J G F f_N = Jᵀ(G⁺F + f_N)`, with `f_N ∈ N(G)` where
used; `J⁻ᵀτ = G⁺F + f_N` is the contact force due to the actuators (p. 301).

**Redundancy (§3.1).** `J̄ = [J; K]` has its rows `(ẋ, v_N)` relabeled by
`e : Fin p ⊕ Fin r ≃ Fin n` to a square matrix (`augmentedJacobian`); `(ẋ, v_N)` is
`Constrained.splitJoin e ẋ v_N`. The book's "rows of `K` span `N(J)`" is stated as `K` onto and
`J Kᵀ = 0`; "orthonormal and perpendicular" as `K Kᵀ = I`, `J Kᵀ = 0`. `Ḡ` (`Ḡᵀ = [[Gᵀ, 0], [0, I]]`)
has rows `(ẋ, v_N)` relabeled by `ew` and columns `(f_c, f_N)` by `ea` (`augmentedGrasp`). The
redundant grasp constraint is `graspPfaffian` (`[J_h −Gᵀ]` with `J_h ∈ ℝ^{m×n}`, the sign of p. 267).
(6.30) carries the object blocks `diag(M_o, 0)`, `diag(C_o, 0)`, `(N_o, 0)` on `(ẋ, v_N)`.

**Tendons (§4).** Extension functions `h : ℝⁿ → ℝᵖ`, coupling matrix `P(θ) = (∂h/∂θ)ᵀ ∈ ℝ^{n×p}`
(`couplingMatrix`, `∂h/∂θ = MapJacobian.jac h θ`); column `i` of `P` is the joint torque of a unit
tension in tendon `i`. `τ = Pf` is the model (the energy argument is a premise). Elastic forces
`f = K(e + h(0) − h(θ))`, stiffness `S(θ) = PK(h(θ) − h(0))`, `Q = PK`. Force-closure (6.34) is
strict positivity of every tension (`IsTendonForceClosure`, tendons indexed by any finite type); the
counts need `n ≥ 1`; (6.35) uses the diagonal stiffness `diag(k)`, `kᵢ > 0`.

**Stacked fingers (6.16).** Fingers are indexed by a finite type `ι`, finger `i` has `n i` joints,
the stacked joints are relabeled by `(Σ i, Fin (n i)) ≃ Fin N`; `θ_{fᵢ} = fingerCoords e θ i`;
`M_f`, `C_f` are `Matrix.blockDiagonal'` relabeled (`stackMat`), `N_f` stacked (`stackVec`); each
finger's inertia depends on its own joints only.

**Substituted Lagrangian (6.15).** `L(r, ṙ, ṡ)` is a function of three arguments without `s`;
partial derivatives are read from its joint Fréchet derivative `DL` (`∂L/∂rᵢ = DL(eᵢ, 0, 0)`,
`∂L/∂ṙᵢ = DL(0, eᵢ, 0)`, `∂L/∂ṡ = DL(0, 0, 1)`), and those of `a` from its Fréchet derivative `Da`
(`∂aⱼ/∂rᵢ = (Da eᵢ)ⱼ`); the last sum of (6.15) is `Σⱼ (∂aⱼ/∂rᵢ) ṙⱼ`.

Recorded 2026-10-26 with commit `1b9a28e`.
Source: MLS printed pp. 31–32, 277–279, 300–310 and Exercise 4(b) (p. 314), read as renders and text
extracts.

**Pose chart of `SE(3)`.** The chart centered at a rotation `R₀` is
`eulerChart R₀ ξ = (R₀ R_z(α) R_y(β) R_z(γ), p)` for `ξ = (p, α, β, γ) ∈ ℝ⁶`, position first
(`Fin 3 ⊕ Fin 3 ≃ Fin 6`) and the ZYZ angles of (2.19) in their printed order; `R₀ = I` is the plain
chart. Its body-velocity Jacobian (rows in twist order `(v, ω)`, columns the six coordinates) is
`[[Rᵀ, 0], [0, E(β, γ)]]`, the columns of `E` being `(−sin β cos γ, sin β sin γ, cos β)`,
`(sin γ, cos γ, 0)`, `(0, 0, 1)`; it satisfies `IsBodyJacobian` along every motion with no restriction,
and its determinant (rows relabeled to `Fin 6`) is `−sin β`. The singular set is `sin β = 0` in
coordinates and, in `SE(3)`, the poses with `zyzRadial(R₀⁻¹ R) = 0` (`R₀⁻¹ R` maps the `z`-axis to `±`
itself); off it, (2.20) applied to `R₀⁻¹ R` is a right inverse with values in `0 < β < π`. The chart is a
local parameterization in the book's sense (a map with invertible Jacobian off the singular set and an
explicit local inverse), not a homeomorphism: it is `2π`-periodic in the angles and the `atan2` inverse
has a branch cut. A pose `g` is reached at nonsingular coordinates by the chart centered at
`R_g R_y(π/2)⁻¹`. Hypothesis wherever the Jacobian is inverted: `sin β ≠ 0`.

**(6.23) and the chart.** The "global versions of the inertial parameters" (p. 279) are the parameters
(6.22) with the object's body-coordinate data `M_g` (constant generalized inertia), `C_g` (the skew
Coriolis matrix of Exercise 4(a)), `N_g` (body wrench coordinates) and the twist-level grasp map `G`. A
chart with Jacobian `Jφ ∈ ℝ^{p×k}` and rate `J̇φ` has the local parameters `M_o = JφᵀM_gJφ`,
`C_o = JφᵀC_gJφ + JφᵀM_gJ̇φ`, `N_o = JφᵀN_g`, `G(x) = JφᵀG`, and the rate `Bd Jφ + J⁻¹GᵀJ̇φ` of `J⁻¹(JφᵀG)ᵀ`;
then the local (6.21) is `Jφᵀ` times the global equation at `V = Jφẋ`, `V̇ = Jφẍ + J̇φẋ`, and the two are
equivalent where `Jφ` is onto.

**The `control` operation.** A controller `RobotController R` of a robot `R` is a law
`u(t, x, ẋ, ẍ, F_c)` (the force applied to `R`; `F_c` the force command of the level above; a desired
trajectory is a parameter of the law) and the attributes `(M̃, C̃, Ñ)` of the controlled robot at each
time, related by equal residual forces: `Mẍ + Cẋ + N − u = M̃ẍ + C̃ẋ + Ñ − F_c` for all arguments. The
controlled robot `R.control K t` is the attributes at `t`; it has the configuration and state of `R`.
The law determines `M̃` and `C̃ẋ + Ñ`, not their split; an acceleration-free law keeps `M̃ = M`. Feedback
laws `u(t, x, ẋ) + F_c` are given the attributes `(M, C, N − u)`, which keep the skew property. The zero
robot (`M = C = N = 0`) is the `Zero` instance of `RobotSystem p`.

**The `attach` operation.** The constraint data `AttachConstraint n p` are the finger configuration
`θ = σ(x)` on the constraint, `J(x) = ∂h/∂θ`, `G(x)` with `Gᵀ = −∂h/∂x` (at `(σ(x), x)`) and the rate
`Bd(x, ẋ)` of `J⁻¹Gᵀ`; the finger velocity is `J⁻¹Gᵀẋ`, the acceleration `J⁻¹Gᵀẍ + Bdẋ`.
`attach F P A` is the robot on the payload coordinates with `M̃ = M_p + GJ⁻ᵀM_fJ⁻¹Gᵀ`,
`C̃ = C_p + GJ⁻ᵀ(C_fJ⁻¹Gᵀ + M_fBd)`, `Ñ = N_p + GJ⁻ᵀN_f` (p. 305 prints `J⁻¹G`; the dimensions and (6.22)
require `J⁻¹Gᵀ`), the finger fields evaluated on the constraint. A list of fingers is one robot by
`RobotSystem.stack` (block-diagonal parameters, relabeling `(Σ i, Fin (n i)) ≃ Fin N`, as (6.16)).
Holonomic data (`IsHolonomic e h`): `h` on the composite configuration relabeled by
`e : Fin p ⊕ Fin n ≃ Fin N`, payload first. The constraint force `λ` has the sign of p. 267
(`J_hᵀλ = τ − (M_fθ̈ + C_fθ̇ + N_f)`, `Gλ = M_pẍ + C_pẋ + N_p`). Hypotheses where used: `J` invertible,
`M_f` symmetric, differentiability along motions, the derivative of `σ` along motions and the rate `Bd`.

**Constrained manipulators (Chapter 4 §6, pp. 200–205).** A constraint surface `h(θ) = 0`,
`h : ℝⁿ → ℝᵏ`, with a parameterization `f : ℝᵐ → ℝⁿ` is the hypothesis structure
`Control.IsSurfaceParametrization h f`: `h` and `f` of class `C²` (MLS: smooth), `f` injective,
`h ∘ f = 0`, the gradients of `h` independent at the points `f(φ)`, `m + k = n`, and `∂f/∂φ` onto
`ker ∂h/∂θ`; from these `J = ∂f/∂φ` is injective. The robot is any `(M, C, N)`
(`Control.RobotSystem n`); the constrained equations are `M θ̈ + C θ̇ + N + (∂h/∂θ)ᵀμ = τ`, the sign
of (6.4), so that under the hybrid law (4.63) the multiplier equals the commanded normal force `λ`.
Motions on the surface are taken in the form `θ = f ∘ φ`, with `θ̈ = Jφ̈ + J̇φ̇`,
`J̇ = MapJacobian.jacDot f φ φ̇`. Lemma 4.2(2) for (4.62) is stated in the congruence form of
Lemma 6.1 and along motions, where `J̇ᵀMJ + JᵀṀJ + JᵀMJ̇` is the derivative of `M̃` given an entrywise
derivative `Ṁ` of `M(f(φ(s)))`. The convergence of (4.63),
deferred by the book, is the closed loop `ë + K_vė + K_pe = 0` with exponential tracking along
Proposition 4.8. The slot of §6.3 and the wall of Chapter 6 Exercise 7 are treated in workspace
coordinates (Exercise 12), where the parameterization is affine; in joint torques the normal term is
`λ∇h(θ) = λJ_p(θ)ᵀn`, not the printed `λn`. Exercise 12(d) compares the two routes for any
joint-space parameterization `f` of the slot defined near a slot position (`p ∘ f` the workspace path
on a neighborhood): the arm's reach is bounded, so no such `f` covers the whole line.

The printed elbow-down parameterization of the slot (p. 204) is
`θ₁(s) = tan⁻¹(s sin α/(l + s cos α)) + cos⁻¹((R + l₁² − l₂²)/(2l₁√R))`,
`θ₂(s) = π + cos⁻¹((l₁² + l₂² − R)/(2l₁l₂))`, `R = s² + 2ls cos α + l²`, with the principal
`tan⁻¹` and `cos⁻¹`; it solves the inverse kinematics where `l + s cos α > 0` and
`(l₁ − l₂)² ≤ R ≤ (l₁ + l₂)²` (hypotheses not printed), and its printed Jacobian is its derivative
under the strict bounds; `R^{3/2}` is written `(√R)³`. Its `θ₂ ∈ [π, 2π]`, the forearm turning
clockwise from the first link. Exercise 12(c) uses the workspace system (4.55) as a robot in `w`
through a map `g` inverse to the arm's position map where used
(`ManipulatorModel.workspaceRobot`), with `K = (cos α, sin α)` and `K̇ = 0`. Exercise 7(b) of
Chapter 6 models the point masses as the arm of Figure 4.4 with `r₁ = l₁/2`, `r₂ = l₂/2` and zero
rotational inertia, the constraint force `∇h(θ)ᵀλ` entering with the sign of (6.4); the exercise
names no gravity, and both the horizontal arm and gravity `g` along `−y` in the plane of the arm
(potential `g(m₁(l₁/2) sin θ₁ + m₂(l₁ sin θ₁ + (l₂/2) sin(θ₁ + θ₂)))`) are stated.

**Nonmanipulable grasps, (6.32)–(6.33) (pp. 290–291).** The hand Jacobian `J_h ∈ ℝ^{m×n}` is injective (the book's "full column rank", p. 290) and the constraint is the library's rectangular `graspPfaffian` `[J_h −Gᵀ]`. The allowable velocities `W(θ, x)` are the preimage under `Gᵀ` of the range of `J_h`; `H ∈ ℝ^{p×l}` is data whose columns span `W` (`SpansAllowable`), and `Ḡ = HᵀG`, so `Ḡᵀ = GᵀH`. The left pseudo-inverse is `J_h⁺ = (J_hᵀJ_h)⁻¹J_hᵀ` with Mathlib's inverse. (6.33) is derived, not defined: the virtual displacements are `δx = Hδw`, `δθ = J_h⁺Ḡᵀδw`, and the parameters are `M̃ = HᵀM_oH + ḠJ_h⁺ᵀM_fJ_h⁺Ḡᵀ`, `C̃ = Hᵀ(C_oH + M_oḢ) + ḠJ_h⁺ᵀ(C_fJ_h⁺Ḡᵀ + M_f(d/dt)(J_h⁺Ḡᵀ))`, `Ñ = HᵀN_o + ḠJ_h⁺ᵀN_f`, `F = ḠJ_h⁺ᵀτ`, with `Ḣ` and `(d/dt)(J_h⁺Ḡᵀ)` actual derivatives along the motion. Corrected printing: p. 291 prints `M_o`, `C_o`, `N_o` and `F = GJ̄_h⁺ᵀτ`; these are exact only for `H = I`.

**The `attach` refinements (p. 305).** The finger configuration on `h(θ, x) = 0` is Mathlib's implicit function of `h(x, θ)` (payload first) at a point where `h` is strictly differentiable and `J = ∂h/∂θ` is invertible (`AttachRegularAt`); it is local and its derivative is the continuous linear map `J⁻¹Gᵀ` with `Gᵀ = −∂h/∂x`. Redundant fingers enter `attach` through internal-motion variables: payload coordinates `w = (x, y)`, `J = J̄_h = [J_h; K_h]` and `G = Ḡ` with `Ḡᵀ = [[Gᵀ, 0], [0, I]]`, so the finger velocity is `J_h⁺Gᵀẋ + K_hᵀẏ` for `K_h` with orthonormal rows perpendicular to those of `J_h`. The net force on the payload is the computed `Gλ + F_e`, `λ = J⁻ᵀ(τ − M_fθ̈ − C_fθ̇ − N_f)` with the sign of p. 267 and `F_e` an external force added to the payload equation; along the attached robot's motion it equals `M_pẍ + C_pẋ + N_p`. Corrected printing: the last factor of p. 305's `M̃ = M_p + GJ⁻ᵀM_fJ⁻¹G` is `Gᵀ` (read so by `attach` already).

**Exercises 1 and 3 (p. 314).** The rolling penny's multipliers are those of (6.4) with the library's sign `d/dt ∂L/∂q̇ − ∂L/∂q = Υ − Aᵀλ`; with that sign `λ = (−mẍ, −mÿ)` on the constraint. The spherical pendulum of Exercise 1 is a point mass at `q ∈ ℝ³` (indices `0, 1, 2` for `x, y, z`, `z` up) on `|q|² = l²`, written as the Pfaffian constraint `A(q) = qᵀ`, and is compared with Example 4.1 (the printed reference to Example 6.1 is read as Example 4.1) through `q = l(sin θ cos φ, sin θ sin φ, −cos θ)`; the comparison is an equivalence off the poles `sin θ = 0`, where the coordinates are singular.

**The two-fingered SCARA grasp, the four-bar linkage and the tendon networks (pp. 291–293, 314–315).** The SCARA grasp of §3.3 uses the hand, contacts and object pose of §5.3: soft-finger contacts at `(0, ∓r, 0)` on the box of Example 5.2, finger bases at `(0, ∓b, 0)`, `R_po = I`, `p_po = (0, 0, a)`, fingertip length zero, finger 1 with links `l₁, l₂` and finger 2 with the library's `l₃, l₄` (Lean joint indices from `0`, so `θ 0 1` is `θ₁₂`). The internal variables are `y = (θ₁₁ + θ₁₂ + θ₁₃, θ₂₁ + θ₂₂ + θ₂₃)` as printed, and `H′` removes the fifth twist coordinate, the object's angular velocity about its `y`-axis through the contacts. Manipulability is Definition 5.5 for the augmented pair `(J̄_h, [[GᵀH′, 0], [0, I]])`; "no internal motions" is the injectivity of `J̄_h`. The four-bar linkage of Exercise 5 is read from its figure as a crank–coupler–slider: the rail through `B` is the `x`-axis with `y` up; link 1 (`l₁`) at `θ₁` from the rail, link 2 (`l₂`) at the relative angle `θ₂`, its end `C` a revolute joint on the slider `T`, and `θ₃` the relative angle of link 3 (rigid with `T`, of length `l₃` along the rail); all angles counterclockwise; joint angles are real numbers, not reduced modulo `2π`, and the crank angle `θ₁ ∈ S¹` is represented by its real lift. The loop constraints are `l₁ sin θ₁ + l₂ sin(θ₁ + θ₂) = 0` and `θ₁ + θ₂ + θ₃ = 0`; for `0 < l₁ < l₂` the branch with the coupler pointing towards the slider is `θ₁ + θ₂ = −arcsin((l₁/l₂) sin θ₁)`. The masses are symbolic point masses `m₁` at the joint of links 1 and 2, `m₂` at `C` and `m₃` at the slider, the links massless, gravity `g` along `−y` and the crank torque at `B`. The tendon networks of Exercise 6 are read from the figure with relative joint angles counterclockwise and pulley radii `r₁`, `r₂` at joints 1 and 2; an extension is the length of the tendon path, with `+r θ` when the path lengthens under a positive rotation (MLS p. 294): passing a joint on the lower side of its pulley, or wrapping counterclockwise onto a pulley it is attached to, adds `r θ`; the upper side, or wrapping clockwise, subtracts it; crossings on the base or along link 1 change no length. In (a) tendon 1 (middle actuator) runs over the joint-1 pulley and is attached to it clockwise, tendon 2 (top actuator) passes under joint 1, crosses to the top of the joint-2 pulley and is attached clockwise, tendon 3 (bottom actuator) passes over joint 1, crosses to the bottom of the joint-2 pulley and is attached counterclockwise; in (b) the lower and upper actuators drive tendons routed as tendons 1 and 2 of (a), and the spring between the links is not part of the actuator kinematics.

## Nonholonomic conventions

Recorded with commit `6342e10`. Source: MLS printed pp. 317–353, read as text; pp. 325, 336, 340,
341 and 343 rendered.

**Carrier and bracket (pp. 321–325).** A vector field is a function `f : E → E` on a real normed
space `E` (MLS: `ℝⁿ`, p. 321); the examples use `Fin n → ℝ` with Mathlib's sup norm. The Lie
derivative is `L_f α = Dα(q) f(q)` for `α : E → F`. The bracket is Mathlib's
`VectorField.lieBracket ℝ f g`, `[f, g](q) = Dg(q) f(q) − Df(q) g(q)`, which is the book's
`(∂g/∂q) f − (∂f/∂q) g` (p. 324). For linear fields `q ↦ Aq`, `q ↦ Bq` it is `q ↦ (BA − AB)q`,
the negative of the ring commutator `⁅A, B⁆ = AB − BA` used by Mathlib and by the library's twist
bracket: on hat matrices, `[x ↦ ξ̂x, x ↦ η̂x] = −(Twist.bracket ξ η)^` and
`[g ↦ ξ̂g, g ↦ η̂g] = −(Twist.bracket ξ η)^ g`, while the left-invariant fields `g ↦ gξ̂` have
`[g ↦ gξ̂, g ↦ gη̂] = g (Twist.bracket ξ η)^`. The curve `t ↦ exp(ξ̂t) g₀` of `TwistTrajectory` is the
integral curve of `g ↦ ξ̂g` through `g₀`. Matrix-valued fields use the entrywise norm (any norm
gives the same derivative) and the matrix flow the operator norm, as `TwistTrajectory` does. The
order of formal exponentials in (8.22)–(8.28) is not fixed here.

**Smoothness.** MLS asks everything to be smooth. Each statement names what it uses: the Jacobi
identity and `L_[f,g] = L_f L_g − L_g L_f` need class `C²` at the point; the product rule, the
bracket of combinations and the integrability argument need differentiability at the point (and a
`C²` map `h`); the filtration exercises and the named statements of Frobenius and Chow take `C^∞`
generators. Mathlib's derivative is zero where a function is not differentiable, so a field with
`tan` or a division (the car, the finger) is used only on the open set where it is smooth.

**Distributions (pp. 325–328).** A distribution is a pointwise subspace `D : E → Submodule ℝ E`;
the distribution spanned by a set `S` of fields is `spanAt S q = span{f(q) : f ∈ S}`. MLS's span
over smooth functions has the same values at each point. Regular means the dimension is constant on
a set. Involutive (`IsInvolutiveOn D U`) means: for fields `f, g` differentiable on `U` with values
in `D` on `U`, `[f, g](q) ∈ D q` on `U`. The generator criterion (`GeneratorsInvolutiveOn S U`)
asks the brackets of the generators to lie in `Δ_q`; it follows from involutivity, and it gives the
bracket of any two combinations of the generators with coefficients differentiable at the point.
The converse for every section of a regular distribution needs local frames and is not formalized.
Where MLS's module structure matters (Exercises 10–11), `InSmoothSpan S` is the span over smooth
functions: finite sums `Σ cₖ wₖ`, `wₖ ∈ S`, `cₖ` smooth. Pfaffian constraints are the library's rows
`A(q)`, with annihilating distribution `Δ_q = ker A(q)`.

**Integrability (pp. 326, 328).** (7.9) is local: `D` is integrable near `q₀` when on an open
neighborhood a smooth `h : E → ℝᵖ` has onto derivative (independent rows `∂hᵢ/∂q`) and
`D q = ker Dh(q)`. For Pfaffian constraints, integrability on a set is the library's kernel
equality (`Constrained.IsIntegrableOn`) with a witness of class `C²` (`IsC2IntegrableOn`). Theorem
7.2's necessity and Proposition 7.4's "only if" are proved. `IsIntegrableAtOfClass n D q₀` is
(7.9) with `h` of class `C^n`; `n = ∞` is `IsIntegrableAt`. Theorem 7.2's "if" is proved with
`C¹` defining maps on finite-dimensional spaces, for distributions regular and involutive on an
open set and spanned near the point by `C¹` fields; Proposition 7.4's "if" near each point with
a `C¹` defining map, for constraints with `C¹` entries and independent rows. The named
`FrobeniusSufficiency E` (`C^∞` generators and defining maps) carries
`[FiniteDimensional ℝ E]`: without it the proposition forces `E` to be finite-dimensional.

**Filtration and Lie algebra (pp. 326, 340–341).** `Δᵢ` is spanned by the generators and the
left-normed brackets `[gⱼ, w]` of a generator with a field spanning `Δᵢ₋₁`; `Δ₀ = 0`, so
`r₀ = 0`. Ranks are dimensions of values at a point; the degree of nonholonomy is the least
`κ ≥ 1` with `rank Δ_κ(q) = rank Δ_{κ+1}(q)`, and regularity is the separate condition
`rank Δᵢ(q) = rank Δᵢ(q₀)` for all `i` and all `q` in a set. `L(g₁, …, g_m)` is the smallest set of
fields containing the generators and closed under sums, real multiples and brackets; its rank at
`q` is the dimension of its values at `q`. Every `Δᵢ(q)` lies in it; the reverse inclusion is not
formalized. Exercise 11 is proved under the module form of `Δᵢ₊₁ = Δᵢ` (every field spanning
`Δᵢ₊₁` a smooth combination of those spanning `Δᵢ`), which implies the book's rank equality; the
passage from equal ranks of a regular filtration is proved on an open set where the filtration
is regular (`IsRegularFiltrationOn`), for smooth generators on a finite-dimensional space:
`Δᵢ₊ⱼ = Δᵢ` there and `Δᵢ` is involutive there.

**Controls and reachable sets (pp. 329–331, 349).** Inputs are piecewise constant: values in `U` on
`[0, T]` and locally constant off finitely many switching times (MLS names no class; the proof of
Proposition 7.7 uses piecewise constant inputs). A trajectory is continuous on `[0, T]` and has
derivative `Σⱼ uⱼ(t) gⱼ(x(t))` off finitely many times. `R^V(q₀, T)` collects the endpoints `x(T)` of
trajectories from `q₀` staying in `V` on `[0, T]`, `R^V(q₀, ≤ T)` the union over `0 < τ ≤ T`, and
local controllability asks `R^V(q₀, ≤ T)` to be a neighborhood of `q₀` for every neighborhood `V`
and every `T > 0`. Reversal needs `U = −U` and rescaling `TU ⊆ U`; MLS states neither.

**Flows (pp. 322–324).** The flow `φ^X_t(q)` of an autonomous field `X` is `φ t 0 q` for a flow
`φ` of the system `fun _ => X` in the sense of `IsDifferentiableFlow` (existence and uniqueness
of solutions, joint continuity, the derivative in the initial state with the variational
equation), for `t ≥ 0`; backward motions are the flow of `−X`: `twoSidedFlow φ φ' t` is
`φ^X_t` for `t ≥ 0` and `φ^{−X}_{−t}` for `t < 0`, with the group property for all real `t`,
`s` and an integral curve of `X` on the whole line; the inverse `φ^{−X}_t` of `φ^X_t` and
commuting flows are stated for nonnegative times. Such flows
exist for every field with a continuous derivative bounded in operator norm on a real Banach
space (MLS: smooth complete fields on `ℝⁿ`). "`φ^f_t` is a local diffeomorphism" (p. 323) is
read as: `φ^X_t` is a bijection differentiable at every point with the differentiable inverse
`φ^{−X}_t`; for a continuous bounded derivative of the field the derivative of `φ^X_t` is
continuous, so `φ^X_t` is strictly differentiable. Commuting flows for `[X, Y] = 0` (p. 324) use Mathlib's bracket and a bound
`‖DX‖ ≤ K`. For a field with a continuous bounded derivative the two-sided flow is of class `C¹` in
`(t, x)`, and so are the composed flows `Φ₁(t₁, ⋯ Φ_k(t_k, x))` (`Φ_k` first); the flow box at
`q` uses a complement `C` of `span{Xᵢ(q)}` and the inverse function theorem. Flows commute where
the bracket vanishes along the trajectories involved, and a field bounded by `M` moves points by
at most `M|t|`. The sufficiency proofs use flows of fields cut off by a smooth bump to compact
support. The `C^∞` "if" half of Theorem 7.2 (`FrobeniusSufficiency E`) remains a named proposition,
used only as a hypothesis of conditional results: (7.9) with a `C^∞` map needs flows of class
`C^∞` in the initial state. Theorem 7.5 (`ChowStatement E`, smooth generators, `U = ℝᵐ`) is
proved on finite-dimensional spaces (next paragraph).

**Chow's theorem (pp. 329–332).** Composed flows `flowSeq Φ x r w s` apply the letter `w₀`
with time `s₀` first and `w_{r−1}` last; times may have either sign, the inputs being
unconstrained, and a word with total time `Σ |sᵢ|` is reached in any time `T > 0` by the
constant inputs `(sᵢ / c) e_{wᵢ}` on `r` consecutive intervals of length `c = T / r`.
Concatenation takes the first input and trajectory on `t ≤ T₁` and the second, shifted by
`T₁`, after. The proof is the maximal-rank argument with flows of the generators only: ranges
of derivatives of composed flows replace the manifolds `N_k` of p. 330, and the bracket
`[gⱼ, Z](y)` is the right derivative at `σ = 0` of `(D_xφ^{gⱼ}_σ(y))⁻¹ Z(φ^{gⱼ}_σ(y))`.
The generators are cut off by a smooth bump outside a ball about `q`, inside which every
trajectory used stays; MLS's linear independence and completeness of the `gⱼ` are not used.
`E` is finite-dimensional (MLS: `ℝⁿ`). `L(g)` is reduced to left-normed brackets by the Leibniz
identity, and the rank condition at `q` gives it near `q` (MLS's Proposition 7.6 assumes it
near `q₀`). Controllability from local controllability at every point asks `U = −U` and
`0 ∈ U`.

**Local frames, annihilating fields and the Philip Hall basis (pp. 325–328, 344–345).** A local
frame of a regular distribution spanned by `g₁, …, g_m` is `k = dim Δ_q` of the generators,
independent and spanning `Δ` near `q`. Proposition 7.3 is stated near a point for
`A : E → (E →L F)` with `A(q)` onto (the one-forms independent at `q`): the fields
`(I − S (A(y) S)⁻¹ A(y)) bⱼ`, with `S` a right inverse of `A(q)` and `bⱼ` a basis of `ker A(q)`,
cut off away from `q`. Lie products are formal brackets of the generators; the Philip Hall
order is by length, then generators by index and brackets of equal length lexicographically
(MLS fixes only condition 2), and condition 3 is read recursively. The basis property is not
formalized.

**Printed errors and domains.** Example 7.4 (p. 336): the text names `θ̇ = u₁` and `φ̇ = u₂`, the
columns of (7.13) give `φ̇ = u₁`, `θ̇ = u₂`; the columns are used. Example 7.7 (p. 341): `g₁`'s
denominator is `I + m(l + d)²` (p. 334), not `I + (l + d)²`, and the printed rank claim near `l = 0`
needs `d ≠ 0`. Example 7.10 (p. 343): `g₄ = (−sin θ/(l cos²φ), cos θ/(l cos²φ), 0, 0)`, and the
fields are independent where `cos φ ≠ 0`, not "when `φ ≠ ±π`". Exercise 4(a) (p. 349): the
unit-time input along `t ↦ q(Tt)` is `T u(Tt)`, not `u(t/T)`. Example 7.12 (p. 345): the
bracket `[g₃, g₁]` is not a Hall product when `g₁ < g₃`; the Hall element is `[g₁, g₃]`, the one
the printed products of length 3 use. Domains: all `q` for the disk
(`ρ ≠ 0`), `cos φ ≠ 0` for the car (`l ≠ 0`), `cos q₁ ≠ 0` for the finger, `l + d ≠ 0` for the
hopper (`I, m > 0`).

**Exercises 2, 16 and 17 (commit `f083494`, pp. 349 and 353).** Exercise 2 is stated for `ρ ≠ 0`
(for `ρ = 0` the constraint is exact) with "nonholonomic" read as not integrable with a `C²` map on
any nonempty open set. Exercise 16's drift at a point is the least-norm solution
`f = Aᵀ(AAᵀ)⁻¹c` of `Af = c` for the stacked constraint rows `A` with `AAᵀ` invertible (a choice;
the input fields span the kernel of `A`). Exercise 17's `σ̄ᵢ` is computed by the printed recursion
with `σ̄₁ = m`, the number of input fields; stages 1–3 of the bound are proved, stage 3 for fields of
class `C²` at the point.

### Chained forms and steering (Chapter 8)

Recorded with commit `66b2eb0`. Source: MLS printed pp. 355–394, read as text; pp. 360, 371, 385 and
387 rendered.

**Model systems.** Brockett's system (8.2), Engel's system (Example 8.4), the second-order system
of p. 363 and the one-chain system (8.7) are drift-free systems on `Fin n → ℝ`; the book's `qᵢ` is
the entry `i − 1` (`q₁` entry `0`, `q_{k+2}` entry `k + 1`), and for p. 363 the order is
`(q₁, q₂, q₁₂, q₁₂₁, q₁₂₂)`. The one-chain fields are `g₁ = e₁ + (0, 0, q₂, …, qₙ₋₁)` and
`g₂ = e₂`; `ad^0_{g₁} g₂ = g₂`, `ad^{k+1}_{g₁} g₂ = [g₁, ad^k_{g₁} g₂]` with the library's bracket,
and `e_j` is the zero vector for `j > n`, so Lemma 8.1 reads `ad^k_{g₁} g₂ = (−1)^k e_{k+2}` for every
`k`. The `m`-input system (8.4)–(8.5) keeps the whole matrix `Y` with `Ẏ = quᵀ − uqᵀ`; the book's
`qᵢⱼ`, `i < j`, are the entries `Yᵢⱼ`.

**Inputs and trajectories of the steering statements (pp. 363–366).** The inputs are the printed
sinusoids, continuous in time, not piecewise constant; trajectories are those of the drift-free
system (`IsTrajectory`: continuous on `[0, 1]`, the equation away from finitely many times).
Every steering statement holds for every trajectory from every initial state; trajectories exist
for continuous inputs (iterated integrals). Algorithm 3's input (`algorithm3Input c a b`) is the
constant `c` on `[0, 1)` and, on `[k, k + 1)`, `k ≥ 1`, the sinusoids of step `k` shifted to start at
`k`; Proposition 8.3 concatenates the steps on `[0, n − 1]`. Points reachable by sinusoidal steering
are not members of the reachable sets of Chapter 7, which use piecewise constant inputs.

**Optimal inputs (pp. 371–373).** The multiplier `p(t)` lies in the dual `E →L[ℝ] ℝ`;
`‖u‖² = Σuᵢ²` (not Mathlib's sup norm). The necessary conditions (8.12)–(8.13) are hypotheses
along a curve on `[0, T]`, with two-sided derivatives at every time of `[0, T]`; optimality, the
existence of an optimal input and the printed rank condition do not enter.

**Corrected printings and domains.** p. 360: with the printed `Λ = [[0, −λ], [λ, 0]]`, the state
from the origin has `q₃(1) = +‖u(0)‖²/λ`, so the cost to reach `(0, 0, a)` is `λa` and, for
`a > 0`, least at `n = +1` (printed `−(1/λ)‖u(0)‖²`, `−λa`, `n = −1`); `‖u(0)‖² = 2πa` stands.
Example 8.3 (p. 371): the printed change of coordinates converts the printed rewritten system,
which is not (7.14) after an input change; for (7.14) the conversion is `z₂ = (1/l) sec³θ tan φ`,
`v₁ = cos θ u₁`, `u₂ = −(3/l) sin²φ sec θ tan θ v₁ + l cos³θ cos²φ v₂`. Algorithm 3 (p. 365): step 2
steers `q_{k+2}` (printed `qₖ`), and the proof's returning coordinates are `qᵢ`, `i < k + 2`
(printed `i < k`). Domains: `cos θ ≠ 0`, `cos φ ≠ 0`, `l ≠ 0` for the car in chained form;
`ρ ≠ 0`, `cos u_f ≠ 0` for the sphere; `λ ≠ 0` for the stationary state of (8.3); `n ≥ 2` for the
filtration level of Proposition 8.2.

**Grasp and sphere (pp. 382–387).** (8.31) is stated at one configuration with a matrix `J_h⁺`
satisfying `J_hJ_h⁺Gᵀ = Gᵀ` (not printed; true for the Moore–Penrose inverse of a manipulable grasp
and for any right inverse). `R_ψ` is the library's `angleMatrix ψ` (p. 250), with `R_ψ² = I`, so the
`R_ψ` of (8.35) equals the `R_ψ⁻¹` that (8.34) gives. The contact angle along a path
`α_f = (u_f, v_f)` solves `ψ̇ = −sin u_f · v̇_f`; Theorem 8.6 is proved for the boundary of a chart
rectangle traversed counterclockwise as four unit-time coordinate segments, with the area
`∫∫ cos u du dv` of the book's area form; Proposition 8.7 is stated for `0 ≤ l < π/2`.

**Follow-ups (commit `acffbdf`, pp. 361–363, 370, 373, 385–387, 392–393; Figures 8.4 and 8.5
rendered).** Exercise 6's `U(t)` is the matrix (Mathlib's `LinearMap.toMatrix'`) of the library's
state-transition map `Φ(t, 0)` of `u̇ = Ω(t)u`, with `Ω` continuous on `[0, T]` and extended by
`Ω(T)` after `T`; `SO(m)` is `Matrix.specialOrthogonalGroup`. Theorem 8.6 holds exactly for
regions `{v₀ ≤ v ≤ v₁, φ₁(v) ≤ u ≤ φ₂(v)}` of the chart, their boundary traversed counterclockwise
in the chart plane (`u_f` horizontal, `v_f` vertical) as four unit-time pieces, the area being the
integral of the book's `cos u du dv` over the region in `ℝ × ℝ` with Lebesgue measure; the cap of
Figure 8.4 contains the pole, and rolling once along its latitude `u₀` with `v_f` decreasing gives
`2π sin u₀ = 2π − Area`, so (8.37) holds for it modulo `2π` (corrected statement). Proposition 8.7
uses the unit sphere resting on the plane `z = 0`; rolling along a straight segment of direction
`d = (cos β, sin β, 0)` is the orientation `R(t) = exp(t â)R₀`, `a = e₃ × d` (spatial angular
velocity `a`, zero contact velocity, zero spin, MLS p. 249), the contact point in body coordinates
is `Rᵀ(−e₃)`, the spherical distance of unit vectors is `arccos⟨p, q⟩`, and Figure 8.5 is placed
with `B` at the origin and `A = (x, 0)`, traversed A → B → C → D → A as drawn, with the right angle
at `B` the figure shows. (8.6) for `m` inputs keeps all index pairs and triples, `q̇ = u`,
`Q̇ₖₗ = qₖuₗ`, `Ẇₖₗₙ = Qₖₗuₙ`, the book's coordinates being the entries with first indices `i < j`;
its "mod Jacobi identity" relation is a first integral. In §3.2, `L_fh` is the library's
`lieDerivative`, fields and functions are `C^∞`, `z_k = L^{n−k}_{g₁}h₂` is entry `k − 1` of the
coordinates, and `Δ₀`'s last generator is `ad^{n−2}_{g₁}g₂` (printed `ad^{n−2}_{g₁}g₁`, which is
zero). The existence of `h₂` is proved when `dim E = n` (MLS: `q ∈ ℝⁿ`), with `h₂` of class
`C¹` near each point; the named statement, which allows every `n`, is false on `ℝ³` with
`n = 4`.

**Exercises (commit `f083494`, pp. 344, 349–353 and 391–394; pp. 391, 392 and 394 rendered).**
"Nilpotent of degree `k`" (pp. 378–379, 391) is read with p. 344's definition: every Lie product of
the generators of length greater than `k` (every bracketing) is the zero field, and `k` is the
least such integer. Controllable is read as the controllability rank condition at every point, as
for Proposition 8.2. Exercise 1's sixth row is read `q̇₆ = ⅙q₁³u₂`; as printed (`u₁`) the system has
the first integral `q₆ − q₁⁴/24`. Exercise 5's state is `(x₀, y₀, x₁, …, x_{n_x}) × (y₂, …, y_{n_y})`,
`y₁ = x₀y₀ − x₁` not a state, and its (b) is read with `x_k` for the printed `q_k`. Exercises 8–9's
"Proposition 8.16" is Proposition 8.4; Exercise 8's normalized input is `s ↦ u(s/c)/c` on `[0, c]`,
`c = ‖u(0)‖`, with least squares optimality among continuous inputs as a hypothesis. (8.38) is
`u̇ = Ω(q, p)u − (pᵀ[f, gᵢ])ᵢ`, the multiplier equation being `ṗ = −pᵀ(∂f/∂q + Σuᵢ∂gᵢ/∂q)`.
Exercise 12's first input is `α₁,₀ + α₁,₁ cos 2πt + α₁,₂ sin 2πt` (the `+` is missing), its
coefficients indexed `0, …, 5` as `(α₁,₀, α₁,₁, α₁,₂, α₂,₀, α₂,₁, α₂,₂)`, and "full rank" is the
linear map of `A(α)` onto `ℝ³`.

## Appendix A conventions

Recorded with commit `c2bad4e`. Source: MLS printed pp. 403–434 and Exercise 17 of Chapter 2
(p. 78), read as text; pp. 428, 431 and 432 also as rendered images.

**Forms on `se(3)`.** `se(3)` is identified with `ℝ⁶` through the twist coordinates `(v, ω)`, linear
part first, as in Chapter 2 and p. 411 (p. 417's `(ω, v)` is a misprint). A bilinear form is its
`6 × 6` matrix, `Ψ(ξ, η) = ξᵀ Ψ η` (`Twist.form`), indexed by `Fin 3 ⊕ Fin 3` like
`Twist.adjointMatrix`. Invariance under change of frame is (A.11), `Ad_hᵀ Ψ Ad_h = Ψ` for every
rigid transform `h` (`Twist.IsAdInvariant`), equivalent to (A.10). Quadratic forms are symmetric;
metrics are positive definite in Mathlib's sense (`Matrix.PosDef`).

**Quadratic forms on `SE(3)`.** A quadratic form on `SE(3)` is read as a form `Ψ_e` on `se(3)`
extended by left translation, `Ψ_g(X, Y) = Ψ_e(g⁻¹X, g⁻¹Y)`, where a tangent vector at `g` is a
`4 × 4` matrix `X` with `g⁻¹X ∈ se(3)`, so `X = gξ̂` (`Twist.leftTranslatedForm`,
`Twist.IsTangentAt`); the tangent maps of `L_h`, `R_h` and `I_h` are `X ↦ hX`, `X ↦ Xh` and
`X ↦ hXh⁻¹`. Smooth dependence on `g` is not stated, and no manifold structure on `SE(3)` is used;
the manifold version is open.

**Length scale.** A change of length scale by `c` maps `(v, ω)` to `(cv, ω)` (`Twist.scaleLength`):
the hyperbolic metric scales by `c`, the Killing form is unchanged, the pitch scales by `c`.

**Killing form.** `⟨ξ₁, ξ₂⟩_K = trace(ad_ξ₁ ∘ ad_ξ₂)` with `ad_ξ = [ξ, ·]` the library's twist
bracket (Example A.8, equal to the matrix commutator of the hat matrices), which gives
`−4 ω₁ · ω₂`. On `so(3)` alone the trace form is `−2 ω₁ · ω₂`; the display of p. 431 uses the
`se(3)` form.

**Vector fields on matrix groups.** Left invariant fields are written on the whole matrix space,
`X_A(g) = gA`, with Mathlib's bracket (the sign of p. 407 and of Chapter 7); brackets of matrix
fields use the entrywise norm, derivatives of the matrix exponential the `L^∞` operator norm, as in
the library's twist exponential. Proposition A.1 is stated for diffeomorphisms of real normed
spaces, the push-forward being `(F_*X)_q = DF(F⁻¹q) X(F⁻¹q)`.

**Manipulability on `6 × 6` matrices.** `σ_min` and `σ_max` of a `6 × 6` matrix with rows `(v, ω)`
are Mathlib's singular values of index 5 and 0 of its Euclidean linear map, as in the
manipulability measures of Chapter 3.

**Volume forms.** A volume form at the identity is an alternating `6`-linear map `Ω` on twists
(`Twist [⋀^Fin 6]→ₗ[ℝ] ℝ`), and its left translate is `Ω_g(X₁, …, X₆) = Ω((g⁻¹X₁)^∨, …, (g⁻¹X₆)^∨)`
for tangent vectors `Xᵢ` at `g` (`Twist.leftTranslatedVolume`), as for the quadratic forms above.
Theorem A.8 is stated for these left translates: right invariance `Ω_{gh}(X₁h, …) = Ω_g(X₁, …)` and
conjugation invariance follow from `det Ad_h = 1` with (A.16) at one tangent space,
`Ω(fξ₁, …, fξ₆) = det f · Ω(ξ)`. Nonvanishing is shown for the determinant form in the twist basis.
Integration of volume forms on a manifold is not stated. **Exponential coordinates of `SO(3)`.**
The chart is `ω ↦ e^{ω̂}` on `ℝ³` into the `3 × 3` matrices; its derivative is
`v ↦ (A(ω)v)^ e^{ω̂}` with `A(ω)` of Example A.12 (at `ω = 0`, `A(0) = I` with Lean's `x / 0 = 0`),
its spatial Jacobian (columns `((∂e^{ω̂}/∂ωⱼ)(e^{ω̂})ᵀ)^∨`) is `A(ω)` and its body Jacobian
`A(ω)ᵀ`. The volume of `SO(3)` is the total mass of the measure on matrices obtained as the image,
under the chart, of the measure on the open ball `‖ω‖ < π` with density `det A(ω)` with respect to
Lebesgue measure; that measure is defined, concentrated on `SO(3)`, invariant under conjugation by
rotations, and not shown to be a Haar measure.

**Log functions.** Example A.15's log function is the twist `(A⁻¹p, ω)` for a chosen `ω` with
`e^{ω̂} = R`; it inverts `exp` (as `Twist.exp ξ 1`) under `sin‖ω‖ ≠ 0`. The single-valued choice
`Twist.seLog` takes `ω = θ ω₀` with the principal angle `θ ∈ [0, π]` of (2.17) and the axis
`ω₀ = (R − Rᵀ)^∨/(2 sin θ)` of (2.18), and inverts `exp` where `sin θ ≠ 0`. Example A.13's series is
not shown to invert the matrix exponential.

**Matrix Lie groups.** The book's Lie groups are sets of real square matrices, subgroups of
`GL(n, ℝ)`: `SO(n)` as Mathlib's `specialOrthogonalGroup`, `SE(3)` as the homogeneous matrices
`[R p; 0 1]` of rigid transforms. The Lie algebra of such a set `G` is the set of matrices `A` with
`exp(tA) ∈ G` for all real `t` (`LieGroup.matrixLieAlgebra`), and the dimension of the group is the
dimension of that Lie algebra. `GL(n, ℝ)` as a Lie group in Mathlib's sense is the unit group of the
continuous endomorphisms of `ℝⁿ` (Euclidean norm, operator norm), isomorphic to the invertible
matrices through `Matrix.toEuclideanCLM`; the pinned Mathlib does not give the structure on the units
of the matrix algebra itself. Its Lie algebra carries Mathlib's bracket of left invariant fields
(`mlieBracket` at the identity, the sign of p. 407), which is the commutator `AB − BA`. Left translation is `L_g(h) = gh` and right translation `R_g(h) = hg`;
a field on a matrix group is a map from the group to matrices, left invariant when `X(gh) = gX(h)`.

**Exponential and logarithm.** The exponential of a matrix Lie group is the matrix exponential; a
one-parameter subgroup is a map `φ` with `φ(0) = I` and `φ(s + t) = φ(s)φ(t)`, and the book's
"connected" one-parameter subgroups are read as those differentiable at `0`. The logarithm of
`SO(3)` near the identity is the principal angle in `[0, π]` times the axis of Example A.14; it
inverts `ω ↦ exp(ω̂)` on the open ball `‖ω‖ < π`.

**One-forms.** As vector fields, one-forms live on real normed spaces `E`: a one-form is a map
`E → (E →L[ℝ] ℝ)`, and the pull back by any map `F` is `(F*β)_p = β_{F(p)} ∘ DF(p)`.

**Volume of `SO(3)`.** The triple-product volume form of p. 431 is pulled back to exponential
coordinates with the density `det A(ω) = 2(1 − cos‖ω‖)/‖ω‖²`, `A(ω)` the matrix of Example A.12,
and integrated over the open ball `‖ω‖ < π` with Lebesgue measure.

**Constraints on `SE(3)`.** A constraint is a function `f : SE(3) → ℝ`; its differential pulled
back to the identity is `ξ ↦ d/dt f(g exp(tξ̂))` at `t = 0`, and left invariance is the printed
equality `L_g^*df(g) = df(e)` for every `g` (p. 429).

**Corrected printings and added hypotheses.** Proposition A.1 is printed for a smooth map but needs a
diffeomorphism for `F_*X` (p. 407); Example A.15's `A⁻¹` and log function need `sin‖ω‖ ≠ 0`, not only `ω ≠ 0`
(p. 414); Example A.23's magnitude is `M_ξ = √(−¼⟨ξ, ξ⟩_K)`, the printed display giving `M_ξ²`
(p. 428); the volume of `SO(3)` for the triple-product form is `8π²`, not `8π³ rad³` (p. 431; the integral
in exponential coordinates is exact and its density is the Jacobian determinant of the chart); `R_g ∘ R_h = R_{hg}`, printed `R_{gh}`
(p. 409); Proposition A.7 fails as printed, in both directions, with the printed definition of a
left invariant constraint (p. 429); the orbit printed `Rⁿ/{0}` is `ℝⁿ \ {0}` (p. 415). Lemma A.2 is applied in the proof
of Proposition A.5 to the block `B`, which need not be symmetric; the library proves the
nonsymmetric form for `n ≥ 3`. Example A.13's norm, which the book does not name, is the operator
norm.
