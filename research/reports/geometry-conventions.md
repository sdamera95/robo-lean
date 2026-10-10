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
first. Twists are a two-field structure `Twist` with fields `linear` and `angular`,
the twist coordinates `(v, ω)` of MLS printed p. 41, eq. (2.30), with the componentwise
real vector-space structure; a `Vec3 × Vec3` value is rejected where a twist is expected
([E010](../../docs/implogs/E010-twist-structure.md)). Wrenches are a distinct two-field
structure `Wrench` with fields `force` and `torque` on the same pattern, so a twist is
rejected where a wrench is expected and conversely
([E008](../../docs/implogs/E008-wrench-carrier-and-library-hygiene.md)). The two carriers
are related only through named maps: the power pairing `Wrench.pair`, the coordinate swaps
`Twist.swapWrench` and `Wrench.toTwist`, and the dual equivalences `Wrench.pairingEquiv`
and `Twist.pairingEquiv`. Neither carrier has a norm, metric or topology; a six-coordinate
norm, if one is ever needed, must be chosen with its metric and length scale and declared
deliberately. The separation is between the typed values `Twist` and `Wrench`, not between their literals: an anonymous constructor `⟨a, b⟩` elaborates as whichever of the two the slot expects, so the component order inside a literal is a convention the types do not check (E010 review, 2026-10-10). The [ledger](mls-coverage-ledger.md)
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

## Kinematics conventions

Recorded 2026-10-09 UTC for increment E009 ([entry](../../docs/implogs/E009-serial-chain-kinematics.md)).
Source: MLS Chapter 3, printed pp. 83–89, 95 and 115–118, extracted as text and,
for pp. 87, 88 and 116–118, inspected as rendered images in this increment. These
are coordinate conventions of the Lean model; they do not certify a physical robot.

**Joint and link numbering.** Joints are numbered from the base to the tip
([p. 83](../../references/MLS.pdf#page=101)). Lean indexes joints by `i : Fin n`,
so Lean joint `i` is the book's joint `i + 1`. Links are indexed by `Fin (n + 1)`;
link 0 is the base, and Lean joint `i` connects link `i` (`Fin.castSucc i`) to
link `i + 1` (`Fin.succ i`), as in "joint i connects links i − 1 and i".

**Joint coordinates and admissible domain.** Joint coordinates are real numbers,
`θ : Fin n → ℝ`. The book's revolute coordinate lives on `S¹`, with `2π`
identified with `0` ([p. 84](../../references/MLS.pdf#page=102)); Lean keeps the
real lift and proves periodicity instead of forming a quotient
(`SerialChain.fk_add_int_mul_two_pi`, for revolute joints with a unit axis). A
real vector therefore names a configuration, but two vectors that differ by `2π`
multiples in revolute coordinates give the same pose; no torus type is defined.
The admissible set `Q` of p. 84 is an explicit `Set (Fin n → ℝ)`: the chain field `SerialChain.admissible` (default: all of `Fin n → ℝ`), and an explicit argument `Q` of every workspace definition. The field is read by the variants `admissibleCompleteWorkspace`, `admissibleReachableWorkspace`, `admissibleDextrousWorkspace` and `admissibleAlternativeDextrousWorkspace`, which fix `Q := c.admissible`, and by the closed-chain joint space `ClosedChain.admissible`; the forward kinematics and the `Q`-parametrized definitions do not read it ([E020](../../docs/implogs/E020-chapter-3-remainder-inverse-kinematics-and-manipulability.md), resolving E009 review F4 by giving the field a use rather than removing it). MLS p. 84 measures angles with a
right-handed convention ("clockwise as viewed along the direction of the axis",
which is the right-hand rule seen with the axis pointing away from the viewer);
it agrees with the positive quarter turn about `+z` above.

**Reference configuration and twists.** The reference configuration is `θ = 0`,
and `SerialChain.toolRef` is `g_st(0)`. Reference joint twists are base-frame
twists at `θ = 0` ([p. 87](../../references/MLS.pdf#page=105)), in the order
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
in `g_ab(θ) = exp(ξ̂θ) g_ab(0)` ([p. 85](../../references/MLS.pdf#page=103)).
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
exponentials applied to `ξᵢ` (eq. (3.54), [p. 116](../../references/MLS.pdf#page=134));
body column `i` is `Ad` of the inverse of (joint exponentials `i..n−1`) `g_st(0)`
applied to `ξᵢ` (eq. (3.55), [p. 117](../../references/MLS.pdf#page=135)).
The `6 × n` matrix view `SerialChain.spatialJacobianMatrix` has rows indexed by
`Fin 3 ⊕ Fin 3` through `Twist.coordinates`: `Sum.inl` rows are `v_x, v_y, v_z`,
`Sum.inr` rows are `ω_x, ω_y, ω_z`, the row order printed on p. 118. The spatial
velocity of the forward-kinematics curve is `RigidTransform.spatialVelocity`,
computed from an actual `HasDerivAt` derivative of the homogeneous pose; the
tool-origin velocity is `ωˢ × p + vˢ`, not `vˢ` alone (p. 117).

**Workspaces.** `completeWorkspace c Q` is the pose image `fk '' Q` (eq. (3.11)),
`reachableWorkspace c Q` the position image (eq. (3.12)), and
`dextrousWorkspace c Q` is `{p | ∀ R, ∃ θ ∈ Q, fk θ = ⟨R, p⟩}` with the printed
quantifier order (eq. (3.13), [p. 95](../../references/MLS.pdf#page=113)), `R`
ranging over all of `SO(3)`. These are pose-reachability sets; they say nothing
about paths, continuity of an inverse, or dynamics.

**Force pullback.** Joint torques equivalent to an end-effector wrench are the pairings
`τᵢ = Wrench.pair F Jᵢ` of the wrench with the Jacobian columns, in matched frames: a
spatial wrench (moment about the base origin, base coordinates) with the spatial Jacobian,
`SerialChain.spatialWrenchTorques` (eq. (3.60), [p. 121](../../references/MLS.pdf#page=139)),
and a body wrench (moment about the tool origin, tool coordinates) with the body Jacobian,
`SerialChain.bodyWrenchTorques` (eq. (3.59)). The two correspond by
`Fˢ = Wrench.transform (fk θ) Fᵇ`, the inverse of `Fᵇ = Ad_gᵀ Fˢ` (eq. (2.67),
[p. 63](../../references/MLS.pdf#page=81)). The matrix forms use `spatialJacobianMatrix` and
`bodyJacobianMatrix` with rows `Sum.inl` = `v`, `Sum.inr` = `ω`, against `Wrench.coordinates`
with `Sum.inl` = `f`, `Sum.inr` = `τ`. The statements are the instantaneous algebraic
identity; the book's frictionless work premise is not formalized
([E011](../../docs/implogs/E011-planar-workspace-certificate-and-force-pullback.md)).

**Planar two-link workspace.** The motion plane of `Examples.planarTwoLink` is the third
coordinate zero, `x 2 = 0` (joint axes `+z`, zero configuration along `+y`), and distances
are the Euclidean norm of `Vec3`. "Unrestricted joints" is `Q = Set.univ`. The annulus,
certificate and radial-band statements are design statements from the assessment, not MLS
results ([ledger C01–C07](mls-coverage-ledger.md#design-certificates-beyond-mls)).

**Planar two-link inverse kinematics.** MLS [p. 98](../../references/MLS.pdf#page=116), eq. (3.16), is stated about the library arm
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

**Supervisor models and the Veil correspondence.** A supervisor model in `RoboLean/Design/` ([E018](../../docs/implogs/E018-veil-pilot-planar-arm-supervisor.md), 2026-10-10) is a
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
only by reading the two files side by side (the table in [E018](../../docs/implogs/E018-veil-pilot-planar-arm-supervisor.md)), not by any kernel. The finite
instance of a Veil model may carry a guard table computed from concrete targets; E018's table is
`planarGuard 2 1` at five tool positions, checked on the Lean side. Veil action names must avoid
the fields `distinct` and `complete` of Veil's generated action-tag class.

**Inverse kinematics subproblems.** A zero-pitch unit twist (MLS
[p. 99](../../references/MLS.pdf#page=117)) is `Twist.revolute ω r` with the hypothesis
`‖ω‖ = 1`, where `r` is a point on the axis; `e^{ξ̂θ} p` is
`(Twist.exp ξ θ).applyPoint p`. With `u = p − r` and `v = q − r`, `PadenKahan.perp ω u` is
`u′ = u − ω ωᵀu` and `PadenKahan.planeAngle ω u v` is
`θ₀ = atan2(ωᵀ(u′ × v′), u′ᵀv′)` (eq. (3.28)), with the library's `Rotation.atan2`
(argument of `x + i y`, in `(−π, π]`, `atan2 0 0 = 0`). Angles are real numbers and
solutions are stated modulo `2π`. Subproblem 2 models intersecting axes by one axis point
`r` for both twists and treats the non-parallel case `ω₁ × ω₂ ≠ 0`; its zero, one or two
solutions are counted as intermediate points `c = e^{ξ̂₂θ₂} p` (eq. (3.21)). Subproblem 3
takes `δ ≥ 0` and the nondegeneracy `u′ ≠ 0`, `v′ ≠ 0`, which the book does not state
([E014](../../docs/implogs/E014-inverse-kinematics-subproblems-and-singularities.md)). MLS
[p. 98](../../references/MLS.pdf#page=116), eq. (3.16), prints the closed-form planar two-link
inverse kinematics; the existence half of the workspace row C02 is its `π − α` branch. The polar-form lemmas of `Rotation.atan2` are `Rotation.sqrt_mul_cos_atan2` and `Rotation.sqrt_mul_sin_atan2` in `Geometry/EulerAngles.lean`; the axis-fixing fact of MLS p. 104 is `Twist.exp_revolute_applyPoint_of_mem_axisLine` ([E020](../../docs/implogs/E020-chapter-3-remainder-inverse-kinematics-and-manipulability.md)).

**Elbow manipulator.** MLS Example 3.2 ([pp. 89–91](../../references/MLS.pdf#page=107)) is `Examples.elbowManipulator l₀ l₁ l₂`, the base
frame with the first axis along `+z` and the arm along `+y` at height `l₀`; the twists are built
with `Twist.revolute` from the axes and points of Fig. 3.4 and agree with the six printed
six-vectors; `g_st(0) = (I, (0, l₁ + l₂, l₀))`. Example 3.5's points are the wrist centre
`p_w = (0, l₁ + l₂, l₀)` and the shoulder point `p_b = (0, 0, l₀)`; `g₁ = g_d g_st(0)⁻¹`
(eq. (3.30), `SerialChain.fk_eq_iff_poe_eq`) and `e^{−ξ̂θ}` is `Twist.exp ξ (−θ)`. Each step is
stated in the form of the corresponding `PadenKahan` subproblem, so its solution theorems apply
directly. The necessary conditions hold for every point of the sixth axis (Step 3) and every point (Step 4); the converse uses a point `p ≠ p_w` of the sixth axis and a point `p′` off it, the points the book prescribes, and characterizes all solutions; the eight-solution count is not formalized.

**Singular configurations.** `SerialChain.IsSingular c θ` means that the `6 × n` spatial
Jacobian matrix has rank less than `min 6 n` ([p. 123](../../references/MLS.pdf#page=141)).
For `n ≤ 6` this is linear dependence of the twist columns, equivalently of the body
Jacobian's columns; for `n > 6` it is the library's extension. For the planar two-link
arm, the p. 123 definition gives no singular configuration when the first link length is
nonzero; the folded configurations `sin θ₂ = 0` are singular for the `2 × 2` position
Jacobian `∂p/∂θ` (`Examples.planarTwoLinkPositionJacobian`, in the sense of eq. (3.64)),
which is a different map. Example 3.12 (three parallel coplanar revolute axes) is `SerialChain.isSingular_of_three_parallel_coplanar_revolute`, for every `n ≤ 6`; the elbow manipulator's reference configuration is its printed instance ([E020](../../docs/implogs/E020-chapter-3-remainder-inverse-kinematics-and-manipulability.md)).

**Manipulability.** The Jacobian of MLS §4.4 ([pp. 127–129](../../references/MLS.pdf#page=145)) is the body Jacobian matrix
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
frame ([p. 133](../../references/MLS.pdf#page=151)). Its joint space `Q′` is the set of
pairs `(θ₁, θ₂)`, each admissible for its chain, with `g₁(θ₁) = g₂(θ₂)` (eq. (3.65)). The
reference tool poses of the two chains are not required to agree; their agreement is
exactly `(0, 0) ∈ Q′`. The differential constraint `J₁ˢθ̇₁ = J₂ˢθ̇₂` (eq. (3.67)) is stated
along trajectories that keep the loop closed near the time considered, and `ρ` (eq. (3.70))
is the dimension of the intersection of the two Jacobian ranges.

**Evidence scope.** The declarations named here were elaborated by the E009
shadow-tree checks and axiom audit recorded in the
[E009 gate](../../docs/implogs/gates/E009/); the integrated `lake build` of the
root import list is root's landing check and is recorded separately. K13 and the planar workspace rows are covered by the [E011 gate](../../docs/implogs/gates/E011/20261009T093129Z/) and the
integrated [E010/E011 gate](../../docs/implogs/gates/E010/20261009T100204Z/), which built them against the `Twist` structure. The subproblem, singularity and closed-chain declarations are covered by the [E014 gate](../../docs/implogs/gates/E014/20261010T002522Z/) and root's integrated gate [E014/20261010T010046Z](../../docs/implogs/gates/E014/20261010T010046Z/). The E020 declarations are covered by the [E020 gate](../../docs/implogs/gates/E020/20261010T211850Z/) and root's integrated gate [E020/20261010T215401Z](../../docs/implogs/gates/E020/20261010T215401Z/).

## Dynamics conventions


Recorded 2026-10-09 10:11:43 UTC for increment E012 (root applied the lead's proposal). Source: MLS Chapter 4, printed pp. 161–178, read this
session as text and, for pp. 162, 168, 176–177, as rendered images. These are conventions of the
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
`0`; its E009 body Jacobian is the book's \(J^b_{sl_k}=[\xi^\dagger_0\cdots\xi^\dagger_k\;0\cdots0]\). The
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
kg·m²) are a convention of the user and are not tracked by types. The linear and angular blocks
of a twist carry different units, so `𝓜` is the only metric used here on twists; `Twist` carries no norm (E010).

**Christoffel symbols and the Coriolis matrix.** For partial derivatives `dM k = ∂M/∂θₖ`,
`Christoffel.symbol dM i j k = (dM k i j + dM j i k − dM i k j)/2` (eq. (4.22)),
`coriolisMatrix dM θ̇ i j = Σₖ Γᵢⱼₖ θ̇ₖ` (eq. (4.23)), and `rate dM θ̇ = Σₖ θ̇ₖ • dM k` (`Ṁ` by the
chain rule). Derivative data are inputs: either the family `dM`, or Fréchet derivatives
`M' i j : (Fin n → ℝ) →L[ℝ] ℝ` of the entries at a configuration, read as
`partials M' k i j = M' i j eₖ`. The skew symmetry of `Ṁ − 2C` (Lemma 4.2(2)) depends on this
choice of `C` (as MLS notes on p. 171) and on symmetric partials, which follow from `M` symmetric at
every configuration.

Recorded 2026-10-10 01:05 UTC for increment E013 (root applied the lead's proposal). Source: MLS
printed pp. 155-178 and p. 209 (Exercise 8), read by the E013 lead as text; p. 175 rendered.

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
real-valued entries and does not depend on that choice. Evidence: the
[E013 gate](../../docs/implogs/gates/E013/20261010T002511Z/) and root's integrated gate
[E013/20261010T005937Z](../../docs/implogs/gates/E013/20261010T005937Z/).

## Stability and control conventions

Recorded 2026-10-10 02:08 UTC for increment E016 (root applied the lead's proposal; integrated gate [E016/20261010T020417Z](../../docs/implogs/gates/E016/20261010T020417Z/)). Source: MLS printed
pp. 179–199, read by the E016 lead as text; pp. 182, 191, 193, 194 rendered.

**Systems and solutions (p. 179).** A system `ẋ = f(x, t)` is `f : ℝ → E → E` with time first,
`f t x`; likewise a Lyapunov function is `V : ℝ → E → ℝ`, `V t x`. `E` is a real normed space; for
`Fin n → ℝ` and products the norm is Mathlib's sup norm (maximum of the components), so
quadratic forms are compared with `‖x‖²` through compactness of the unit sphere
(`QuadraticBounds`), not through eigenvalues. A solution from `t₀` (`Stability.IsSolution f t₀ x`)
is continuous on `[t₀, ∞)` and has the actual derivative `f t (x t)` at every `t > t₀`. Initial
times are `t₀ ≥ 0` (MLS's `ℝ₊`). Existence and uniqueness are not assumed or proved: every
stability notion quantifies over all solutions, so a theorem says nothing about whether solutions
exist; the constant solution at an equilibrium is the only solution exhibited.

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
motion are Lagrange's equations for `L = T − V` with generalized force `τ − Nₑ` (E013's predicate),
equivalent to (4.47) with symmetric link inertias. The state is `(θ, θ̇) ∈ ℝⁿ × ℝⁿ`; under a feedback
law `τ = u(t, θ, θ̇)` the closed loop is `f(t, (q, v)) = (v, M(q)⁻¹(u − C(q, v)v − N(q, v)))` with
Mathlib's `Matrix.inv`, used only under the hypothesis that `M(q)` is positive definite.

**Gains and control laws (§5).** Gains are real `n × n` matrices; "positive definite" is Mathlib's
`Matrix.PosDef`, which includes symmetry (MLS writes `K > 0`). Computed torque is (4.49) with a
desired trajectory given by `θ_d` and actual derivatives `θ_d'`, `θ_d''` at every time. The PD
set-point law formalized is `τ = N(θ, θ̇) − K_v θ̇ − K_p(θ − θ_d)` (compensation of `N`, (4.53) with
`θ̇_d ≡ 0`); the bare law (4.51) is defined and shown to have `θ_d` as a rest point only where
`N(θ_d, 0) = 0`. Exact cancellation of the model is assumed throughout; sampled implementation,
actuator limits and model error are outside these statements.
