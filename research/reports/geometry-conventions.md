# Geometry conventions for RoboLean

Initially recorded 2026-10-09 00:29:36 UTC. This document specifies the rigid-transform,
twist, velocity, and wrench conventions and identifies the checked subset. Implementation
evidence belongs in the [coverage ledger](mls-coverage-ledger.md); this document
alone does not certify a Lean implementation or a physical model.

The source is Murray, Li, and Sastry, [MLS](../../references/MLS.pdf), Chapter 2.
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
[pp.23-25](../../references/MLS.pdf#page=41) and
[p.35, equations (2.21)-(2.22)](../../references/MLS.pdf#page=53).

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
Sources: [rotation composition (2.3), p.25](../../references/MLS.pdf#page=43)
and [rigid composition/inverse, p.37](../../references/MLS.pdf#page=55).

A coordinate conversion describes the same physical point in two frames: this
is the passive interpretation of `g_AB`. The same affine formula can also
describe an active displacement, with both the initial and final coordinates
expressed in one fixed frame A. In that interpretation the point moves. Each
theorem or example must state the intended meaning. MLS distinguishes these
interpretations for the twist exponential on
[p.42, equation (2.37)](../../references/MLS.pdf#page=60); that active
motion acts on an initial pose by left multiplication.

## Rotations, points, and displacement vectors

A rotation satisfies `Rᵀ R = R Rᵀ = I` and `det R = 1`. The positive quarter
turn about `+z` sends `e_x` to `e_y`, `e_y` to `-e_x`, and fixes `e_z`.
This specifies the sign without a viewing-direction ambiguity; it matches
MLS's [`R_z` matrix on p.31](../../references/MLS.pdf#page=49).
Orientation uses `e_x × e_y = e_z` and hat convention `hat(a) b = a × b`,
as on [p.26, equations (2.4)-(2.7)](../../references/MLS.pdf#page=44).

Point action and displacement-vector action are distinct:

\[
g(q)=Rq+p,\qquad g_*(v)=Rv,\qquad
g(q)-g(r)=g_*(q-r).
\]

Translation affects points but cancels in differences. A point plus a
displacement is a point; the difference of two points is a displacement.
Adding two point-coordinate tuples is arithmetically possible in the initial
representation but has no intrinsic affine meaning. Source:
[MLS p.36](../../references/MLS.pdf#page=54).

The homogeneous representation is

\[
H(g)=\begin{bmatrix}R&p\\0&1\end{bmatrix},\qquad
\bar q=\begin{bmatrix}q\\1\end{bmatrix},\qquad
\bar v=\begin{bmatrix}v\\0\end{bmatrix}.
\]

The last coordinate distinguishes the actions. The block-matrix bridge
uses index type `Fin 3 ⊕ Fin 1`; a displayed `4 × 4` matrix orders its
coordinates as `x, y, z, homogeneous`. Source:
[pp.36-37, equations (2.23)-(2.24)](../../references/MLS.pdf#page=54).

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
**Verified — formal statements:** the [I2 build and 85-declaration audit](../../docs/implogs/gates/E003/20261009T015317Z/summary.json)
checks `Rotation.act_cross`, `RigidTransform.applyVector_cross`,
`Vec3.hat_mulVec`, `Vec3.hat_act`, and the real linear equivalence
`Vec3.hatLinearEquiv`. It covers all vectors including zero; `hat_vee` requires
the skew condition. The [ledger](mls-coverage-ledger.md#implementation-evidence-i2) gives the
source mapping and evidence limits.

Lengths mean `‖v‖₂ = sqrt(v_x² + v_y² + v_z²)`; distance means
`dist(q,r) = ‖q-r‖₂`. An unadorned function type `Fin 3 → ℝ` must not
silently supply the norm for a robotics distance theorem. MLS's Euclidean
distance and cross-product preservation targets are Propositions 2.2 and 2.7
on [p.26](../../references/MLS.pdf#page=44) and
[p.38](../../references/MLS.pdf#page=56).

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

**Verified - formal statements:** the [I3 build and audit](../../docs/implogs/gates/E004/20261009T022521Z/summary.json)
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

**Verified - formal statements:** the [final build and audit](../../docs/implogs/gates/E007/20261009T042046818411474Z/summary.json)
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
product and norm-one group, not a quaternion-to-rotation or half-angle bridge.

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
first. Both carriers use pairs of Euclidean `Vec3` coordinates; their product
norm is not declared to be a canonical physical magnitude. The [ledger](mls-coverage-ledger.md)
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

Sources: [p.41, equations (2.30)-(2.31)](../../references/MLS.pdf#page=59),
[pp.54-55, equations (2.53), (2.55), (2.57)-(2.58)](../../references/MLS.pdf#page=72).
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
[pp.61-63, equations (2.65)-(2.67)](../../references/MLS.pdf#page=79).
The dual pairing is `f·v + τ·ω`; with velocity units it is instantaneous power,
whose time integral is work. MLS denotes the pairing by `δW`; RoboLean's
`Wrench.pair` states the instantaneous pairing. I4 proves preservation under
compatible `Wrench.transform` and `Twist.adjoint` transformations. The later
interval-work theorems below retain actual derivative and integrability premises.

### Checked subset and assumptions

**Verified - formal statements:** the [I4 build and audit](../../docs/implogs/gates/E005/20261009T032143837813448Z/summary.json)
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

The [final formal gate](../../docs/implogs/gates/E007/20261009T042046818411474Z/summary.json)
and its [source review](../../docs/implogs/gates/E007/20261009T042046818411474Z/source-statement-review.md)
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
[Appendix A inventory](../../docs/implogs/gates/E007/20261009T042046818411474Z/appendix-source-inventory.md)
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
Common-normal existence, principal-angle identification, and the omitted
parallel/intersecting/infinite-pitch cases remain separate. The ledger records
X60 as Unverified with partial evidence for the conditional formula.

## Source inspection and evidence scope

**Verified - source transcription only:** rendered inspection of printed
pp.23, 25, 26, 31, 35-38, 41-42, 54-55, and 61-63 of
[MLS.pdf](../../references/MLS.pdf) supports the displayed coordinate-direction,
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

**Verified — additional source transcription, 2026-10-09:** the I2 reviewer
re-rendered and opened printed pp.26–28 and 37–38 to compare cross-product, hat,
skew-space, conjugation, and vector-action formulas with the named declarations.
The [source-inspection record](../../docs/implogs/gates/E003/20261009T015317Z/review.md) and preserved
renderings bound that review.

**Verified - additional bounded source inspection, I3:** the reviewer opened
rendered printed pp27-31 and every page pp39-69, preserved with the
[source review](../../docs/implogs/gates/E004/20261009T022521Z/source-statement-review.md) and
[P2 inventory](../../docs/implogs/gates/E004/20261009T022521Z/provenance/robo-e004-source-p2-ledger.md).
The I4 normalization now proves rescaling of the full twist `(v,ω)`.
The later screw APIs distinguish zero, finite pitch, and pure translation;
parameters remain signed while norm-based magnitude scales by abs(θ).
Reciprocal-system power and dimension statements do not establish physical
contact feasibility.

**Verified - additional bounded source inspection, I4:** the
[source-statement review](../../docs/implogs/gates/E005/20261009T032143837813448Z/source-statement-review.md) maps the new declarations
to MLS printed pp39–44 and 51–64 and records the unit-axis premise, full-twist normalization,
full-turn exclusion, derivative hypotheses, and instantaneous-power scope.
The [ledger](mls-coverage-ledger.md#implementation-evidence-i4) distinguishes
these checked statements from partial and remaining source obligations.

The [final source-statement review](../../docs/implogs/gates/E007/20261009T042046818411474Z/source-statement-review.md)
records the subsequent rotation, logarithm, Euler, bracket, screw, and work scope,
including the named domain restrictions and remaining partial obligations.

**Unverified here:** numerical refinement, physical interpretation of a particular
robot, and user acceptance. Named formal-statement evidence is linked above and
in the coverage ledger; this document does not establish full implementation
conformance with the book.
