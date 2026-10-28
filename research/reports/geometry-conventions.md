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
The singular middle-angle endpoints `β=0,π` are outside that inverse theorem;
no global smooth or unique Euler chart is supplied.
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

**Proposition 4.10's `ε` (p. 195).** The smallness of `ε` depends on the region of initial errors when
`C ≠ 0`: for the planar two-link arm every `ε > 0` leaves a state where the corrected `V̇` is positive
(an instance). The formal conclusion stays semiglobal, global for constant inertia.

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
hypothesis. Only the "if" direction holds in the library's model.

**Figure 5.13.** The book defines no axes; the library uses the triangle `(0, 0)`, `(1, 0)`,
`(1/2, √3/2)`, contacts `(s, 0)` and `(t/2, t√3/2)` measured from the shared vertex.

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
