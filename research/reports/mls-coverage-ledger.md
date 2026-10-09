# MLS coverage ledger

Initial inventory: 2026-10-08 America/New_York. Source: Murray, Li, and Sastry,
*A Mathematical Introduction to Robotic Manipulation*, [local PDF](../../references/MLS.pdf).
This starts the inventory step in the [library roadmap](lean-library-roadmap.md).
See [geometry conventions](geometry-conventions.md) for the coordinate contract.

## Scope and counting

This is a **selected-item inventory**, not a full-book inventory. The original
59 obligations (28 rotation, 15 rigid-transform, and 16 selected kinematics
rows) retain their IDs. The I3 source review adds 63 rows, X01-X63, for twists,
rigid exponentials, screws, velocities, adjoints, wrenches, and reciprocal systems
from Chapter 2 pp39-69, giving 122 selected rows through I5.
[I6](#implementation-evidence-i6) adds four bounded Appendix A rows, L01-L04,
so the current selected denominator is 126; this is not an estimate of the
book's total content. The X rows were all Unverified at I3; I4 checks 36,
I5 adds 11, and I6 adds 15 more. X60 retains a checked conditional result and
remains Unverified as a whole row. Source inventory is separate from proof evidence.

Definitions, structures, theorems, specifications, and derived bridges have
distinct labels. Each stable ID names one selected obligation; one source
proposition may require several Lean lemmas, and one implementation theorem may
support several statements. Counts measure selected obligations, not independent
theorems, implementation effort, or book coverage. No full-book percentage is
justified. The [I1 gate](#implementation-evidence-i1) supports 21 obligations,
[I2](#implementation-evidence-i2) adds six, and
[I3](#implementation-evidence-i3) adds R13-R18, giving 33 through I3.
[I4](#implementation-evidence-i4) adds 36, giving 69 through I4.
[I5](#implementation-evidence-i5) adds 15, giving 84 through I5.
[I6](#implementation-evidence-i6) adds 19 existing-row results and four new
Appendix results: 107 selected obligations are Verified in full (30 definitions,
three structures, 63 theorem obligations, and 11 bridges). At I6 the other 19 remained
Unverified: R27-R28, X60 in full, and K01-K16. [I7](#implementation-evidence-i7)
adds K01-K12 and K14-K16 (six definitions, eight theorem obligations, one
specification), so 122 of the 126 selected obligations are Verified in full and four
remain Unverified: R27-R28, X60 in full, and K13. [I8](#implementation-evidence-i8)
records the distinct `Wrench` carrier and changes no row status. These are selected-item counts,
not independent Lean theorem counts or a whole-book percentage.

Pages are `printed / PDF`, with PDF pages one-based. All inspected main-text
pages satisfy PDF page = printed page + 18. Source reading and rendering do not
establish a Lean result. A Verified row must identify the declaration, assumptions,
pinned toolchain, and check. User acceptance is separate.

## Representation and module map

Names below are intended targets unless accompanied by implementation evidence.
The initial representation selected by the implementation lead is
`RoboLean.Vec3 := EuclideanSpace ℝ (Fin 3)`,
`RoboLean.Rotation := Matrix.specialOrthogonalGroup (Fin 3) ℝ`, and a
`RoboLean.RigidTransform` with rotation and translation fields. Matrix action
uses `Matrix.toEuclideanLin`; public actions are `Rotation.act`,
`RigidTransform.applyPoint`, and `RigidTransform.applyVector`. The default norm
on a Pi coordinate type must not silently replace Euclidean norm. Frame indices and separate point/vector types
are deferred; the named actions retain their distinct meanings.

| Alias | Intended module | Role |
| --- | --- | --- |
| RT | `RoboLean/Geometry/RigidTransform.lean` | Initial rotation and rigid-transform API |
| H | `RoboLean/Geometry/Homogeneous.lean` | Pair/homogeneous-matrix bridge |
| CP | `RoboLean/Geometry/CrossProduct.lean` | Euclidean cross product and proper-rotation/vector preservation |
| HT | `RoboLean/Geometry/Hat.lean` | Hat/vee, skew-matrix linear equivalence, rotation conjugation |
| HP | `RoboLean/Geometry/HatPowers.lean` | Euclidean hat square/cube identities |
| RD | `RoboLean/Geometry/Rodrigues.lean` | Rodrigues equalities for the actual matrix exponential |
| X | `RoboLean/Geometry/Twist.lean` | Independent twist matrix carrier and hat/vee linear equivalence |
| SE | `RoboLean/Geometry/TwistExp.lean` | Actual rigid exponential; closed forms, normalization, and translation-coefficient invertibility in companion modules |
| SV | `RoboLean/Geometry/RigidVelocity.lean` | Actual pose derivatives and spatial/body velocities; rotation and composition companion modules |
| AD | `RoboLean/Geometry/TwistAdjoint.lean` | Coordinate adjoint, conjugation, inverse, and representation laws |
| WR | `RoboLean/Geometry/Wrench.lean` | Distinct two-field wrench carrier, independent power pairing, inverse-adjoint transpose, and common-frame wrench sums |
| E | `RoboLean/Geometry/RotationExp.lean` | Skew exponential SO(3) membership and fixed-axis trajectories; axis-angle surjectivity remains future |
| C | `RoboLean/Geometry/ElementaryRotations.lean`, `EulerAngles.lean` | Elementary families and ordered ZYZ product/generic inverse |
| Q | `RoboLean/Geometry/UnitQuaternion.lean` | Scalar/vector product and norm-one group; rotation bridges remain open |
| LB | `RoboLean/Geometry/TwistBracket.lean`, `AdjointBracket.lean` | Coordinate/matrix bracket, Lie identities, and derived adjoint covariance |
| K | `RoboLean/Kinematics/SerialChain.lean` | Joint and forward-kinematics semantics |
| J | `RoboLean/Kinematics/Jacobian.lean` | Derivative, twist, force interfaces |
| W | `RoboLean/Kinematics/Workspace.lean` | Quantified workspace definitions |
| P | `RoboLean/Examples/PlanarTwoLink.lean` | Future two-revolute example |

Coordinates are real columns in right-handed orthonormal frames. `g_ab` sends B
coordinates to A; `g_ab * g_bc` applies `g_bc` first. For `g=(p,R)`, point action
is `p+Rq`, vector action is `Rv`, and distances are Euclidean. Twists use `(v,ω)`.
These conventions interpret code; they do not certify measured frame labels.

## Rotation obligations, Chapter 2

| ID / kind | Source printed / PDF | Intended statement/module | Assumptions/conventions | Dependencies or missing bridge | Formal status | Statement divergence |
| --- | --- | --- | --- | --- | --- | --- |
| R01 definition | p24 / 42, eq2.2 | RT: `Rotation` represents real `SO(3)` | `R Rᵀ=I`, determinant `+1` | Pinned special-orthogonal-group subtype | Verified I1 (definition) | Initial alias fixes dimension 3; MLS also defines `SO(n)` |
| R02 theorem | p23 / 41, eq2.1 | RT: `Rotation.mul_transpose`, `Rotation.transpose_mul` | `R : Rotation` | Real conjugate-transpose/transpose bridge | Verified I1 (theorem) | No intended mathematical change |
| R03 structure | p24 / 42, group axioms | RT: inherited `Group Rotation` structure | Real square matrices, determinant `+1` | Reuse mathlib group and coercion facts | Verified I1 (structure) | Reuse structure rather than duplicate its proofs |
| R04 theorem | p24 / 42, inverse paragraph | RT: `Rotation.inv_val` identifies inverse matrix with `Rᵀ` | `R : Rotation` | R02; inverse/coercion API | Verified I1 (theorem) | No intended mathematical change |
| R05 definition | p25 / 43, coordinate action | RT: `Rotation.act`, `act_apply` implement `q ↦ Rq` | B-to-A column coordinates | Matrix-to-Euclidean-linear-map bridge | Verified I1 (definition) | Point/vector semantics share a coordinate type initially |
| R06 theorem | p25 / 43, eq2.3 | RT: `Rotation.act_mul` proves `(R₁R₂)q=R₁(R₂q)` | Compatible frames; right factor acts first | Matrix multiplication/action compatibility | Verified I1 (theorem) | Initial types do not enforce frame compatibility |
| R07 definition | p26 / 44, eq2.4 | HT: `Vec3.hat`, first row `(0,-a₃,a₂)` | Right-handed cross product | Explicit Fin-3 matrix construction | Verified I2 (definition) | Actual name is `Vec3.hat`; same coordinate formula |
| R08 theorem | p26 / 44, eq2.5 | HT: `Vec3.hat_mulVec` proves `hat(a)b=a×b` | Euclidean coordinates via `WithLp.ofLp` | CP: `Vec3.cross`, `cross_coordinates` | Verified I2 (theorem) | Coordinate equality explicitly transports the existing Euclidean vectors |
| R09 theorem | p26 / 44, Lemma2.1 eq2.6 | CP: `Rotation.act_cross` proves `R(v×w)=(Rv)×(Rw)` | `R : Rotation`, hence determinant `+1` | Triple-product determinant identity, inner-product preservation | Verified I2 (theorem) | Orthogonality alone does not exclude reflections; proof explicitly uses `det_eq_one` |
| R10 theorem | p26 / 44, Lemma2.1 eq2.7 | HT: `Vec3.hat_act` proves `hat(Rw)=R hat(w) Rᵀ` | `R : Rotation`; arbitrary `w : Vec3` | R04, R08-R09, matrix-action extensionality | Verified I2 (theorem) | Equality is reversed relative to the printed display; same identity |
| R11 theorem | p26 / 44, Proposition2.2(1) | RT: `Rotation.dist_act` preserves Euclidean distance | Arbitrary points in `Vec3` | Inner-product/isometry bridge | Verified I1 (theorem) | A raw Pi-norm theorem would be a different claim |
| R12 bridge | pp27-28 / 45-46, eq2.10 and text | HT: `Vec3.hatLinearEquiv : Vec3 ≃ₗ[ℝ] SkewMatrix3` | Real skew-transpose condition; all vectors including zero | `mem_skewMatrix3_iff`, hat/vee inverses, additivity and scalar compatibility | Verified I2 (bridge) | Genuine linear equivalence onto independent `skewAdjoint` matrices; no normalization premise |
| R13 theorem | p28 / 46, Lemma2.3 eq2.12 | HP: `Vec3.hat_sq` proves `hat(a)^2=outer(a,a)-‖a‖² I` | Euclidean norm; arbitrary `a`, including zero | `Vec3.outer` entry is `aᵢaⱼ`; Euclidean norm-square identity | Verified I3 (theorem) | No normalization premise |
| R14 theorem | p28 / 46, Lemma2.3 eq2.13 | HP: `Vec3.hat_cube` proves `hat(a)^3=-‖a‖² hat(a)` | Arbitrary real `a`, including zero | R13 and `Vec3.hat_mulVec_self` | Verified I3 (theorem) | No intended mathematical change |
| R15 theorem | p27 / 45, eqs2.8-2.9 | E: `Rotation.hasDerivAt_exp_act` and `exp_zero_act` give the exponential trajectory solution and initial value | Any constant axis and initial point; unit axis for parameter-as-angle interpretation | Actual matrix-exponential derivative transported to Euclidean action | Verified I3 (theorem) | Proves solution property, not uniqueness or physical rate calibration |
| R16 theorem | p28 / 46, eq2.14 | RD: `Vec3.exp_hat_of_norm_eq_one` proves unit-axis Rodrigues equality with `NormedSpace.exp` | `‖ω‖=1`, any real parameter | R14; trigonometric derivatives; integrating factor and mean-value theorem | Verified I3 (theorem) | Normalization retained explicitly; formula is not the definition of exponential |
| R17 theorem | p28 / 46, display after eq2.14 | RD: `Vec3.exp_hat_of_ne_zero` plus `exp_hat_zero` cover nonzero and zero axes | `ω≠0` for denominator formula; any real parameter | R16 and Euclidean normalization/rescaling | Verified I3 (theorem) | Replace denominator-unsafe printed domain `‖ω‖≠1`; norm-one axes are included |
| R18 theorem | p29 / 47, Proposition2.4 | E: `Rotation.matrix_exp_mem`, packaged by `expSkew`, proves skew exponential lies in `SO(3)` | `Aᵀ=-A` for any real 3-by-3 matrix; any real scalar in `expSkew` | Exponential transpose/inverse; determinant nonnegativity via half-parameter square | Verified I3 (theorem) | Proves determinant +1; no unit premise or dependence on Rodrigues |
| R19 theorem | pp29-30 / 47-48, Proposition2.5 | E: unit-axis exponential representation exists for every rotation | `R : Rotation` | Identity, generic-angle, half-turn cases | Verified: [I5](#implementation-evidence-i5); `Rotation.exists_unit_axis_angle_le_pi`, `Rotation.exists_unit_exp` | Printed extraction omits explicit half-turn case; existence target retained |
| R20 theorem | p30 / 48, eqs2.17-2.18 | E: generic trace/entry axis recovery | `θ=acos((trace R-1)/2)`, `sin θ≠0` | Trace bounds, trigonometry, R16 | Verified: [I5](#implementation-evidence-i5); `Rotation.principalAngle`, `Rotation.principalAngle_mem_Icc`, `Rotation.trace_mem_Icc`, `Rotation.genericAxis`, `Rotation.genericAxis_spec` | Printed `θ≠0` is insufficient at `π`; no global logarithm |
| R21 theorem | p31 / 49, Theorem2.6 | E: axis-angle existence with angle in `[0,2π)` | Proper rotation; unit axis also chosen for identity | R19, angle normalization | Verified: [I5](#implementation-evidence-i5); `Rotation.exists_unit_axis_angle` | No uniqueness or global smooth selection |
| R22 definition | p31 / 49, elementary rotations | C: coordinate matrices `Rx`, `Ry`, `Rz` in `SO(3)` | Radians; right-handed positive angles | Trigonometry and membership proofs | Verified: [I5](#implementation-evidence-i5); `Rotation.xMatrix`, `Rotation.yMatrix`, `Rotation.zMatrix`, `Rotation.exp_xAxis_val`, `Rotation.exp_yAxis_val`, `Rotation.exp_zAxis_val`, `Rotation.xMatrix_mem`, `Rotation.yMatrix_mem`, `Rotation.zMatrix_mem`, `Rotation.elementary_matrix_det` | Exact quarter-turn instance does not prove the family |
| R23 theorem | p32 / 50, eq2.19 | C: ZYZ product equals expanded matrix | `Rz(α) Ry(β) Rz(γ)` in that order | R22, finite matrix multiplication | Verified: [I6](#implementation-evidence-i6); `Rotation.zyzMatrix`, `Rotation.zyz`, `Rotation.zyz_val` | No intended mathematical change |
| R24 theorem | p32 / 50, eq2.20 | C: generic ZYZ inverse reconstructs rotation | `sin β≠0`, explicit `atan2` branches | Branch-aware inverse-angle API | Verified: [I6](#implementation-evidence-i6); `Rotation.atan2`, `Rotation.zyzRadial`, `Rotation.zyzAlpha`, `Rotation.zyzBeta`, `Rotation.zyzGamma`, `Rotation.sin_zyzBeta`, `Rotation.zyzBeta_mem_Ioo`, `Rotation.zyz_inverse` | Local inverse only; singular orientations separate |
| R25 theorem | p33 / 51, quaternion product | C: scalar/vector quaternion product formula | Fixed `(scalar,vector)` split | Quaternion and cross-product APIs | Verified: [I6](#implementation-evidence-i6); `QuaternionCoordinates.ofScalarVector`, `QuaternionCoordinates.vector`, `QuaternionCoordinates.mul_formula`, `QuaternionCoordinates.vector_mul` | Inverse/group claims need nonzero input, unlike printed all-quaternion prose |
| R26 structure | p34 / 52, unit-quaternion paragraph | C: unit quaternions form a group | Norm 1 | Quaternion norm multiplicativity | Verified: [I6](#implementation-evidence-i6); `UnitQuaternion`, `mem_unitQuaternion_iff`, `UnitQuaternion.ofNormOne`, `UnitQuaternion.norm_val`, `UnitQuaternion.val_ne_zero`, `UnitQuaternion.mul_val`, `UnitQuaternion.inv_val` | Reuse pinned structure if available |
| R27 theorem | p34 / 52, axis-angle quaternion | C: `(cos(θ/2),ω sin(θ/2))` represents axis rotation | `‖ω‖=1` | R16, quaternion rotation map | Unverified | Reverse extraction needs `sin(θ/2)=0` endpoint cases |
| R28 theorem | p34 / 52, `Q_ac=Q_ab·Q_bc` | C: quaternion-to-rotation map preserves multiplication | Unit quaternions, common frame convention | R25-R27, matrix representation | Unverified | Retain double cover; no bijection with `SO(3)` |

Proposition 2.2(2) repeats R09's cross-product conclusion and receives no duplicate
row. Rotation-coordinate topology, other Euler orders, exercise proofs, and a
full quaternion conversion API remain outside this selected inventory.

## Rigid-transform obligations, Chapter 2

| ID / kind | Source printed / PDF | Intended statement/module | Assumptions/conventions | Dependencies or missing bridge | Formal status | Statement divergence |
| --- | --- | --- | --- | --- | --- | --- |
| T01 definition | p35 / 53, eq2.21 | RT: `RigidTransform` defines the rotation/translation coordinate pair | Translation in `Vec3`, proper rotation | R01 | Verified I1 (definition) | Coordinate representation only; no characterization of arbitrary distance/orientation-preserving maps |
| T02 definition | p35 / 53, eq2.22 | RT: `RigidTransform.applyPoint` implements `g(q)=p+Rq` | `g_ab` sends B coordinates to A | R05; affine action | Verified I1 (definition) | Named action distinguishes points within common coordinate type |
| T03 theorem | p36 / 54, vector-action display | RT: `RigidTransform.applyPoint_sub_applyPoint` proves the induced vector action | `v=s-r`, arbitrary representatives | T02, linearity | Verified I1 (theorem) | Vector action adds no translation |
| T04 definition | p36 / 54, homogeneous point | H: `homogeneousPoint` embeds point as `(q,1)` | Last coordinate 1 | `HomogeneousIndex := Fin 3 ⊕ Fin 1` | Verified I1 (definition) | Fourth coordinate represented by `Sum.inr 0`; spatial coordinates by `Sum.inl` |
| T05 definition | p36 / 54, homogeneous vector | H: `homogeneousVector` embeds vector as `(v,0)` | Last coordinate 0 | Same indexing as T04 | Verified I1 (definition) | Distinct from point embedding |
| T06 definition | p36 / 54, eq2.23 | H: `RigidTransform.toHomogeneous` gives `[[R,p],[0,1]]` | Proper rotation and translation | Block-matrix construction | Verified I1 (definition) | Representation of pair core, not core type itself |
| T07 theorem | p36 / 54, display before eq2.23 | H: `RigidTransform.toHomogeneous_mulVec_point` relates point actions | T04, T06 | T02, block multiplication | Verified I1 (theorem) | No intended mathematical change |
| T08 theorem | pp37-38 / 55-56, vector-action display | H: `RigidTransform.toHomogeneous_mulVec_vector` relates vector actions | T05, T06 | T03, block multiplication | Verified I1 (theorem) | No intended mathematical change |
| T09 theorem | p37 / 55, eq2.24 | RT: `mul_rotation`, `mul_translation`, `mul_applyPoint` expose pair composition and its action | Right factor acts first; compatible frame meanings | R03, R06, T02 | Verified I1 (theorem) | Homogeneous-matrix multiplication equality is separately required by T15 |
| T10 theorem | p37 / 55, group item2 | RT: `Group RigidTransform`, `one_applyPoint`, `one_applyVector` give identity laws | Source pair ordering | T02, composition | Verified I1 (theorem) | No intended mathematical change |
| T11 theorem | p37 / 55, group item3 | RT: `inv_rotation`, `inv_translation_coordinates` and group laws give `(-Rᵀp,Rᵀ)` as inverse | Orthogonality | R04, composition | Verified I1 (theorem) | Homogeneous inverse is also checked by `RigidTransform.toHomogeneous_inv` in H |
| T12 structure | p37 / 55, group items1,4 | RT: `Group RigidTransform` packages closure and associativity | Rotation closure and translation algebra | R03, T09-T11 | Verified I1 (structure) | Structure packaged as one selected obligation |
| T13 theorem | p38 / 56, Proposition2.7(1) | RT: `RigidTransform.dist_applyPoint` preserves point distances | Euclidean metric, arbitrary points | R11, T03 | Verified I1 (theorem) | Exact real geometry, no floating-point guarantee |
| T14 theorem | p38 / 56, Proposition2.7(2) | CP: `RigidTransform.applyVector_cross` preserves cross products | Proper rotation; free-vector action | R09, `RigidTransform.applyVector` | Verified I2 (theorem) | Translation is absent from vector action; no analogous point-action claim |
| T15 bridge | pp36-37 / 54-55, derived from eqs2.23-2.24 | H: `RigidTransform.homogeneousEquiv`, `toHomogeneousHom` relate pair and constrained matrix representations | Last row `(0,0,0,1)`, rotation block in `SO(3)` | T06-T11, injectivity, reconstruction, homomorphism | Verified I1 (bridge) | An equivalence plus matrix multiplication compatibility; no target subgroup instance claimed |

The pair definition and homogeneous equivalence do not characterize every
distance- and cross-product-preserving map as such a pair. That converse remains
un-inventoried; R09/T14 separately track cross-product preservation by the
coordinate action. Named fields are `rotation`, `translation`, while MLS writes
the mathematical pair `(p,R)`.

Supporting action/inner-product lemmas do not inflate this inventory. Example 2.1
begins on p38; its full derivation is not selected here. The later fixed-line
examples are explicitly inventoried in X14-X15 below and remain Unverified. The current exact quarter-turn composition
probe is a convention check, not a substitute for that example or Chapter 3 FK.

## Twist, adjoint, and wrench obligations, Chapter 2

The [I3 source review](../../docs/implogs/gates/E004/20261009T022521Z/source-statement-review.md)
opened every rendered printed page pp39-69/PDF57-87. These 63 new rows comprise
20 definitions, 36 theorem obligations, and seven bridges. All were Unverified
at I3; I4 supports 36 full rows, I5 adds 11, and I6 adds 15, giving 62 full
X rows. X60 retains a certificate-conditional check and remains Unverified
as a whole source obligation.
The [preserved proposal](../../docs/implogs/gates/E004/20261009T022521Z/provenance/robo-e004-source-p2-ledger.md)
records the original source inventory and page-inspection commands.

Module labels now follow the checked I4 implementation: X = `Geometry/Twist.lean`,
SE = `Geometry/TwistExp.lean` and its closed-form/Jacobian companions,
SV = `Geometry/RotationVelocity.lean`, `Geometry/RigidVelocity.lean`, and their
trajectory/composition companions, AD = `Geometry/TwistAdjoint.lean`, and
WR = `Geometry/Wrench.lean`. EX names selected examples. SC has a checked
attribute layer in `Geometry/TwistScrew.lean`; coordinate reciprocal systems
are in `Geometry/Reciprocal.lean`. Geometric screw and axis rows retain their
individual statuses. All paths are beneath `RoboLean/`. The homogeneous index
is `Fin 3 ⊕ Fin 1`; twist order is `(v,ω)` and wrench order is `(f,τ)`.

### Twist algebra and rigid exponentials

| ID / kind | Source printed / PDF | Intended statement/module | Assumptions/conventions | Dependencies or missing bridge | Formal status | Statement divergence |
| --- | --- | --- | --- | --- | --- | --- |
| X01 definition | p40 / 58, eq2.29 | X: `se(3)` as a linear part and an independently skew angular matrix | Real coordinates; no unit/nonzero premise | HT skew carrier; real product module | Verified: [I4](#implementation-evidence-i4); `se3Submodule`, `Se3`, `mem_se3Submodule_iff` | Distinguish abstract twist coordinates from their homogeneous matrix representation |
| X02 definition | p41 / 59, eqs2.30-2.31 | X: twist hat and vee with hat(v,ω)=[[hat(ω),v],[0,0]] | Linear coordinates first; last row all zero | HT; block matrices; six-coordinate or product carrier | Verified: [I4](#implementation-evidence-i4); `Twist.hat`, `Twist.vee`, `Twist.hat_angular`, `Twist.hat_linear`, `Twist.hat_lowerLeft`, `Twist.hat_lowerRight` | No bottom-right 1; that entry belongs to rigid transforms |
| X03 bridge | pp40-41 / 58-59, eqs2.29-2.31 and inverse-operator prose | X: real linear equivalence between `(v,ω)` and the independent `se(3)` matrix carrier | Bottom row zero, upper-left block skew | Both inverse laws, linearity, X01-X02 | Verified: [I4](#implementation-evidence-i4); `Twist.vee_hat`, `Twist.hat_vee`, `Twist.hatLinearEquiv` | Reverse inverse needs the defining matrix conditions, as with hat/vee for rotations |
| X04 theorem | p39 / 57, eqs2.25-2.26 | X/SC: axis rotation field `ṗ=ω×(p-q)` equals homogeneous action of twist `(-ω×q,ω)` | Fixed axis and q; unit ω for unit angular speed | CP, HT, homogeneous point/vector distinction | Verified: [I4](#implementation-evidence-i4); `Twist.offset_axis_velocity`, `Twist.hat_offset_axis_mulVec_point` | Algebraic identity does not require unit norm; physical speed interpretation does |
| X05 theorem | p40 / 58, displayed exponential solution after Fig2.5 | SE/SV: constant-twist trajectory solves the homogeneous linear ODE and has the prescribed initial point | Constant twist; real time; initial homogeneous point | Matrix-exponential derivative and action; X02 | Verified: [I4](#implementation-evidence-i4); `Twist.hasDerivAt_exp_toHomogeneous`, `Twist.hasDerivAt_homogeneousPoint_exp_applyPoint`, `Twist.hasDerivAt_exp_applyPoint`, `Twist.exp_zero_applyPoint` | Solution property, uniqueness, and physical rate interpretation are distinct obligations; this row selects the solution property |
| X06 theorem | pp40-41 / 58-59, eqs2.27-2.28 and 2.32 | SE: exp of `(v,0)` has rotation I and translation `θv` | Any v and real θ, including v=0 | Nilpotent matrix power; exponential series | Verified: [I4](#implementation-evidence-i4); `Twist.exp_hat_pure_translation`, `Twist.exp_hat_of_angular_eq_zero`, `Twist.exp_pure_translation` | Unit v only when θ is interpreted as signed translation distance |
| X07 theorem | pp41-42 / 59-60, Proposition2.8 | SE: exponential of every real twist matrix belongs to the constrained homogeneous `SE(3)` representation | Any twist and real θ | R18; block exponential or X06/X09/X10; T15 | Verified: [I4](#implementation-evidence-i4); `Twist.matrix_exp_blocks`, `Twist.matrix_exp_mem`, `Twist.toHomogeneous_exp` | Covers zero and unnormalized angular components, not merely the normalized closed form |
| X08 theorem | p42 / 60, eq2.35 | SE: exponential commutes with conjugation by a rigid transform | Invertible homogeneous matrix; arbitrary twist and real scalar | Matrix.exp_conj; homogeneous inverse; X02 | Verified: [I4](#implementation-evidence-i4); `RigidTransform.matrix_exp_conj` | Use the actual exponential; the equality is not a new definition |
| X09 theorem | pp41-42 / 59-60, eqs2.33-2.36 | SE: normalized rigid-exponential translation is `(I-R)(ω×v)+ω(ω·v)θ`, R=exp(θhat(ω)) | Explicit ‖ω‖=1; arbitrary v and θ | R13-R18, X08, block powers | Verified: [I4](#implementation-evidence-i4); `Twist.exp_hat_of_angular_norm_eq_one`, `Twist.exp_translation_of_angular_norm_eq_one` | Box eq2.36 prints only ω≠0, but its derivation assumes unit ω on p41; preserve that stronger premise |
| X10 bridge | p41 / 59, normalization prose before eq2.33; p42 / 60, eq2.36 | SE: reduce arbitrary nonzero ω to X09, rescaling the entire twist | Set a=‖ω‖>0, ξ'=(v/a,ω/a), θ'=aθ; separate ω=0 | X03 scalar compatibility; R17; X06/X09 | Verified: [I4](#implementation-evidence-i4); `Twist.exp_hat_normalize_angular`, `Twist.angular_norm_normalize`, `Twist.exp_normalize_angular`, `Twist.exp_hat_of_angular_eq_zero` | Rescaling ω alone would change translation; both v and ω must be divided by a |
| X11 bridge | p42 / 60, eq2.37; p49 / 67, eq2.45 | SE/EX: an active twist displacement acts on points in one fixed frame and on an initial pose by left multiplication | Fixed reference frame; body point constant in body coordinates | T09/T15, X05, homogeneous action | Verified: [I4](#implementation-evidence-i4); `Twist.toHomogeneous_exp_mul`, `Twist.exp_mul_applyPoint`, `Twist.hasDerivAt_exp_mul_applyPoint`, `Twist.exp_zero_mul_applyPoint` | Active displacement and passive coordinate conversion need separate stated meanings |
| X12 theorem | pp42-43 / 60-61, Proposition2.9 | SE: every rigid transform is the exponential of a twist | Real SE(3); separate identity, translation, and nonidentity rotation cases | R19; X06/X09/X13 | Verified: [I5](#implementation-evidence-i5); `RigidTransform.exists_twist_exp`, `RigidTransform.exists_twist_exp_one` | Existence does not supply a global smooth or unique logarithm; inherit the rotation half-turn case requirement |
| X13 theorem | p43 / 61, eq2.38 and following nonsingularity argument | SE: `A=(I-exp(θhat(ω)))hat(ω)+θωωᵀ` is nonsingular | ‖ω‖=1 and 0<θ<2π | R16, axis/orthogonal-plane decomposition or determinant formula | Verified: [I4](#implementation-evidence-i4); `Twist.translationJacobian`, `Twist.det_translationJacobian`, `Twist.det_translationJacobian_ne_zero`, `Twist.isUnit_translationJacobian`, `Twist.translationJacobian_mulVec_injective`, `Twist.translationJacobian_mulVec_inv_mulVec`, `Twist.det_translationJacobian_two_pi` | θ≠0 alone is insufficient at nonzero full turns; orthogonal nullspaces need an actual injectivity argument |
| X14 theorem | pp43-44 / 61-62, Example2.2 absolute-pose formula | EX: reproduce the stated absolute-pose exponential coordinates for the fixed-line mechanism | Rz(α), pose translation `(-l₂sin α,l₁+l₂cos α,0)`; α not a full turn | X09/X13, finite matrix algebra | Verified: [I6](#implementation-evidence-i6); `Twist.exp_zAxis_translation`, `Twist.exp_absolute_z_pose` | Printed α≠0 does not exclude nonzero multiples of 2π; denominator `1-cos α` requires an explicit restriction |
| X15 theorem | p45 / 63, Example2.2 relative transform; pp49-50 / 67-68, Example2.3 | EX: relative motion has constant twist `((l₁,0,0),(0,0,1))`, and exp times the initial pose gives the displayed pose | Fixed +z axis through `(0,l₁,0)`; real angle | X09/X11; exact reference-pose composition | Verified: [I6](#implementation-evidence-i6); `Twist.exp_offset_z_mul_initial` | Relative twist is simpler than the absolute-pose logarithm; can cover θ=0 by direct formula even where the example says θ≠0 |

### Screw semantics

| ID / kind | Source printed / PDF | Intended statement/module | Assumptions/conventions | Dependencies or missing bridge | Formal status | Statement divergence |
| --- | --- | --- | --- | --- | --- | --- |
| X16 definition | pp45-46 / 63-64, eq2.39 and Definition2.2 | SC: screw motion data with directed axis, finite pitch or a pure-translation case, and a motion parameter | Unit direction; axis point; pitch finite or separately tagged infinite | Affine line; explicit finite/infinite representation | Verified: [I6](#implementation-evidence-i6); `ScrewMotion`, `ScrewMotion.finite`, `ScrewMotion.translation`, `ScrewMotion.stationary`, `ScrewMotion.toRigidTransform`, `ScrewMotion.parameter` | Do not encode infinity as a real number; distinguish signed parameter from norm-based magnitude |
| X17 theorem | pp46-47 / 64-65, eqs2.40-2.41 | SC: screw point action is `q+R(p-q)+hθω`; homogeneous translation `(I-R)q+hθω`; pure translation is `p+θv` | Unit direction, finite pitch in rotating case; pure translation separately | RT action, R16/R18; X16 | Verified: [I6](#implementation-evidence-i6); `ScrewMotion.toRigidTransform`, `Twist.exp_fromScrew_applyPoint`, `Twist.exp_pure_translation_applyPoint` | Algebraic formula includes θ=0; rotation and translation about the same axis commute but need an explicit argument if claimed |
| X18 theorem | pp47-48 / 65-66, eq2.40 comparison and Proposition2.10 | SC/SE: a finite-pitch screw is generated by `(-ω×q+hω,ω)` and a pure translation by `(v,0)` | Unit direction; finite/infinite cases explicit | X06/X09/X17; vector triple-product identity | Verified: [I6](#implementation-evidence-i6); `ScrewMotion.generator`, `ScrewMotion.generator_isUnit`, `ScrewMotion.exp_generator`, `Twist.exp_fromScrew` | This is the geometric-to-exponential agreement theorem, not just a coordinate definition |
| X19 definition | p47 / 65, eq2.42 | SC: twist pitch `(ω·v)/‖ω‖²` for ω≠0, infinite-pitch tag when ω=0 | Nonzero denominator in finite branch | Euclidean inner product; case split | Verified: [I5](#implementation-evidence-i5); `ScrewPitch`, `ScrewPitch.finite`, `ScrewPitch.infinite`, `ScrewPitch.stationary`, `Twist.finitePitch`, `Twist.screwPitch`, `Twist.screwPitch_of_angular_ne_zero`, `Twist.screwPitch_pure_translation`, `Twist.screwPitch_zero`, `Twist.screwPitch_eq_stationary_iff`, `Twist.screwPitch_eq_infinite_iff` | Zero twist needs a separate degeneracy policy; an infinite-pitch tag alone does not provide a directed axis |
| X20 definition | p47 / 65, eq2.43 | SC: twist axis through `(ω×v)/‖ω‖²` in direction ω; pure translation axis chosen through origin in direction v | ω≠0, or ω=0 and v≠0 | Affine line; X19 | Verified: [I6](#implementation-evidence-i6); `axisLine`, `mem_axisLine_iff`, `axisLine_finrank`, `Twist.finiteAxis`, `Twist.mem_finiteAxis_iff`, `Twist.finiteAxis_finrank`, `Twist.pureTranslationAxis`, `Twist.mem_pureTranslationAxis_iff`, `Twist.pureTranslationAxis_finrank`, `Twist.screwAxis`, `Twist.screwAxis_eq_none_iff` | The all-zero twist yields a singleton from the printed set expression, not a directed line; exclude it or record degeneracy |
| X21 definition | p48 / 66, eq2.44 | SC: twist magnitude is ‖ω‖ when ω≠0 and ‖v‖ otherwise | Nonnegative norm-based quantity | Euclidean norm, X01 | Verified: [I5](#implementation-evidence-i5); `Twist.screwMagnitude`, `Twist.screwMagnitude_nonneg`, `Twist.screwMagnitude_eq_zero_iff`, `Twist.screwMagnitude_smul` | For a unit twist, magnitude of θξ is abs(θ); printed M=θ requires θ≥0 or a separate signed convention |
| X22 definition | p49 / 67, first paragraph | SC: unit twist means ‖ω‖=1, or ω=0 and ‖v‖=1 | This is not the Euclidean norm of six coordinates | X21; two explicit branches | Verified: [I5](#implementation-evidence-i5); `Twist.IsUnitTwist`, `Twist.isUnitTwist_iff_magnitude_eq_one`, `Twist.screwMagnitude_smul_of_unit` | No frame-invariant Euclidean 6D norm follows |
| X23 theorem | p49 / 67, axis-point paragraph | SC: replacing q by q+λω leaves the finite-pitch twist and motion unchanged | Same directed axis, arbitrary real λ | Cross-self zero; axis fixed by its rotation; X17/X18 | Verified: [I5](#implementation-evidence-i5); `Twist.fromScrew`, `Twist.fromScrew_axis_shift`, `Twist.exp_fromScrew_axis_shift` | Representative independence is needed before treating an affine line as the underlying object |
| X24 theorem | p49 / 67, axis-point paragraph after eq2.40 reference | SC: points on the screw axis move by `hθω` | Finite pitch; point on axis; unit direction | X17; rotation fixes axis | Verified: [I6](#implementation-evidence-i6); `Twist.exp_fromScrew_applyPoint_on_axis` | Pure translation is its separately represented limiting case, not evaluation of a real formula at h=∞ |
| X25 theorem | p49 / 67, Theorem2.11 (Chasles) | SC/SE: every rigid displacement admits an axis rotation followed by parallel translation | Proper rigid motion; identity and translation cases explicit | X12 and X18-X20 | Verified: [I6](#implementation-evidence-i6); `RigidTransform.exists_screw_motion`, `RigidTransform.IsScrewDisplacement`, `RigidTransform.isScrewDisplacement` | This is a finite-displacement existence theorem; no unique global screw/logarithm or trajectory equivalence is claimed |

### Velocities and adjoints

| ID / kind | Source printed / PDF | Intended statement/module | Assumptions/conventions | Dependencies or missing bridge | Formal status | Statement divergence |
| --- | --- | --- | --- | --- | --- | --- |
| X26 theorem | pp51-52 / 69-70, Lemma2.12 | SV: `ṘR⁻¹` and `R⁻¹Ṙ` are skew | Differentiable real rotation curve at the time in question | Product/transpose derivative; R02/R04; derivative interface on matrix coercions | Verified: [I4](#implementation-evidence-i4); `Rotation.spatialVelocity_skew`, `Rotation.bodyVelocity_skew` | Make differentiability and time-domain assumptions explicit; mere pointwise SO(3) membership is not enough |
| X27 definition | p52 / 70, eqs2.48-2.49 | SV: spatial/body angular velocities via vee of `ṘR⁻¹` and `R⁻¹Ṙ` | Same trajectory and time; body frame instantaneously oriented | X26; HT inverse | Verified: [I4](#implementation-evidence-i4); `Rotation.spatialAngularVelocity`, `Rotation.bodyAngularVelocity`, `Rotation.hat_spatialAngularVelocity`, `Rotation.hat_bodyAngularVelocity` | Define using explicit derivative evidence or state differentiability wherever the definition is used |
| X28 theorem | p52 / 70, eq2.50 | SV: spatial/body angular velocities satisfy `ωᵇ=R⁻¹ωˢ` | Real rotation trajectory | X26-X27; R10 | Verified: [I4](#implementation-evidence-i4); `Rotation.bodyAngularVelocity_eq` | Angular velocity conversion rotates coordinates; it is not a six-coordinate twist transformation |
| X29 theorem | pp51-52 / 69-70, eqs2.46-2.47 and 2.51-2.52 | SV: a fixed body point has spatial velocity `ωˢ×qₐ` and body-expressed physical velocity `ωᵇ×q_b` in pure rotation | Body coordinate q_b constant; differentiable rotation curve; common origin | X27-X28; HT action; chain rule | Verified: [I4](#implementation-evidence-i4); `Rotation.hasDerivAt_act`, `Rotation.hasDerivAt_act_spatial`, `Rotation.body_velocity_eq_cross` | Body-expressed physical velocity is not the derivative of the constant body coordinates |
| X30 theorem | p53 / 71, Example2.4 | EX: Rz(θ(t)) has spatial and body angular velocities `(0,0,θ̇)` | Differentiable real θ(t); fixed +z axis | Rotation coordinate family; derivative trigonometry; X27 | Verified: [I4](#implementation-evidence-i4); `Rotation.hasDerivAt_exp_val_comp`, `Rotation.zRotation_val`, `Rotation.zRotation_angularVelocities` | Example checks derivative/sign conventions and equality special to this fixed-axis motion |
| X31 definition | pp54-56 / 72-74, eqs2.53,2.55,2.59-2.60 | SV: define spatial/body twists by `ġg⁻¹` and `g⁻¹ġ` | Differentiable pose curve; linear coordinates first | X02; homogeneous curve derivative; RT inverse | Verified: [I4](#implementation-evidence-i4); `RigidTransform.spatialVelocity`, `RigidTransform.bodyVelocity`, `RigidTransform.spatialVelocity_linear`, `RigidTransform.bodyVelocity_linear` | Spatial linear part is `ṗ-ωˢ×p`; body linear part is `Rᵀṗ` |
| X32 bridge | pp54-55 / 72-73, block products preceding eqs2.53,2.55 | SV: the two velocity matrices are in independent se(3), and have the displayed coordinate components | Differentiable pose curve | X26; block derivatives; X03/X31 | Verified: [I4](#implementation-evidence-i4); `RigidTransform.derivative_lowerLeft`, `RigidTransform.derivative_lowerRight`, `RigidTransform.hat_spatialVelocity`, `RigidTransform.hat_bodyVelocity`, `RigidTransform.spatial_matrix_mem_se3`, `RigidTransform.body_matrix_mem_se3` | A generic derivative ġ is not itself a twist matrix; multiply by the inverse first |
| X33 theorem | pp54-55 / 72-73, eqs2.54,2.56 | SV: physical point velocity is `ωˢ×qₐ+vˢ` and body-expressed velocity is `ωᵇ×q_b+vᵇ` | Body point constant; compatible frames; differentiable curve | X31-X32; homogeneous action and chain rule | Verified: [I4](#implementation-evidence-i4); `RigidTransform.hasDerivAt_applyPoint_spatial`, `RigidTransform.body_point_velocity` | At body origin, spatial velocity is ṗ, not generally vˢ; body coordinates of that velocity are vᵇ |
| X34 definition | p55 / 73, eq2.58 | AD: `Ad_(p,R)=[[R,hat(p)R],[0,R]]` on twist coordinates | `(v,ω)` column order | HT, RT, 2-by-2 blocks of Fin-3 matrices | Verified: [I4](#implementation-evidence-i4); `Twist.adjoint`, `Twist.adjointMatrix`, `Twist.adjointMatrix_mulVec` | The translation-dependent upper-right block is essential |
| X35 bridge | pp55-56 / 73-74, eq2.57 and Lemma2.13 | AD: `hat(Ad_g ξ)=H(g)hat(ξ)H(g)⁻¹`, so conjugation preserves se(3) | Any rigid transform and any twist | X03/X34, R10, T15 | Verified: [I4](#implementation-evidence-i4); `Twist.hat_adjoint`, `Twist.conjugation_mem_se3`, `Twist.se3AdjointEquiv_apply` | A genuine conjugation/coordinate equivalence, not a definition of both sides by the same formula |
| X36 theorem | p56 / 74, inverse display before Lemma2.13 | AD: inverse adjoint matrix equals Ad of the inverse transform, with explicit block formula | Proper R; arbitrary translation | RT inverse; X34-X35 | Verified: [I4](#implementation-evidence-i4); `Twist.adjoint_inv`, `Twist.adjointMatrix_inv`, `Twist.adjointMatrix_inv_blocks` | Orthogonality of the full 6-by-6 adjoint is not asserted |
| X37 bridge | pp55-56 / 73-74, derived from eq2.58/Lemma2.13 and rigid composition | AD: adjoint is a linear representation, `Ad_(gh)=Ad_g Ad_h` and `Ad_1=I` | Same composition direction as T09 | X35; injectivity of twist hat; homogeneous composition | Verified: [I4](#implementation-evidence-i4); `Twist.adjoint_one`, `Twist.adjoint_mul`, `Twist.adjointMatrix_one`, `Twist.adjointMatrix_mul`, `Twist.adjointMatrixHom` | Derived reusable bridge; these representation laws are not separately numbered propositions in the inspected pages |
| X38 theorem | pp55-56 / 73-74, eqs2.57 and 2.61 | SV/AD: `Vˢ=Ad_g Vᵇ` | Differentiable pose at the same time; compatible definitions | X31-X35 | Verified: [I4](#implementation-evidence-i4); `RigidTransform.spatialVelocity_eq_adjoint_body` | No Euclidean twist-norm invariance follows |
| X39 theorem | pp56-57 / 74-75, Example2.5 | EX: one-axis offset mechanism has `vˢ=(l₁θ̇,0,0)`, `vᵇ=(-l₂θ̇,0,0)`, and both angular parts `(0,0,θ̇)` | Exact displayed pose with constant l₀,l₁,l₂; differentiable θ | X31-X33, finite derivatives | Verified: [I5](#implementation-evidence-i5); `Examples.planarPose_toHomogeneous`, `Examples.hasDerivAt_planarPose`, `Examples.planarPose_spatialVelocity`, `Examples.planarPose_bodyVelocity` | Spatial/body linear components differ even though their angular components coincide |
| X40 theorem | pp57-58 / 75-76, Section4.3 displays | SV/SE: for `g(t)=exp(θ(t)hat(ξ))g₀`, `Vˢ=θ̇ξ` and `Vᵇ=θ̇ Ad_(g₀⁻¹) ξ` | ξ,g₀ constant; θ differentiable | Exponential chain rule; X08/X31/X35 | Verified: [I4](#implementation-evidence-i4); `RigidTransform.hasDerivAt_toHomogeneous_exp_mul`, `RigidTransform.spatialVelocity_exp_mul`, `RigidTransform.bodyVelocity_exp_mul` | Constant twists do not imply constant velocity unless θ̇ is constant; no unit premise needed for the algebra |
| X41 theorem | pp58-59 / 76-77, Proposition2.14 | SV: spatial velocity of a composed frame chain is `V_acˢ=V_abˢ+Ad_(g_ab)V_bcˢ` | Differentiable compatible frame curves | Product rule; X31/X35 | Verified: [I4](#implementation-evidence-i4); `RigidTransform.hasDerivAt_toHomogeneous_mul`, `RigidTransform.spatialVelocity_mul` | Relative rates and frame labels must be stated explicitly |
| X42 theorem | p59 / 77, Proposition2.15 | SV: body velocity of a composed chain is `V_acᵇ=Ad_(g_bc⁻¹)V_abᵇ+V_bcᵇ` | Differentiable compatible frame curves | Product rule; X31/X35 | Verified: [I4](#implementation-evidence-i4); `RigidTransform.bodyVelocity_mul` | The adjoint uses inverse of the second transform |
| X43 theorem | p59 / 77, eqs2.62-2.63 | SV: a constant change of spatial reference gives `V_acˢ=Ad_(g_ab)V_bcˢ` and `V_acᵇ=V_bcᵇ` | g_ab constant in time | X41-X42; derivative of constant | Verified: [I4](#implementation-evidence-i4); `RigidTransform.hasDerivAt_toHomogeneous_const_mul`, `RigidTransform.spatialVelocity_const_mul`, `RigidTransform.bodyVelocity_const_mul` | Fixed relative frame is the algebraic premise; do not omit it or infer it from a frame name |
| X44 bridge | p59 / 77, eq2.64, combined with p42 / 60, eq2.35 | AD/SE: re-expressing a constant twist by Ad_g intertwines its entire exponential motion under fixed conjugation | Fixed g; any twist and parameter | X08/X35; scalar linearity | Verified: [I4](#implementation-evidence-i4); `Twist.matrix_exp_adjoint`, `Twist.exp_adjoint`, `Twist.exp_adjoint_applyPoint` | Derived frame-equivariance bridge; avoids recounting Lemma2.13 as a new independent theorem |
| X45 theorem | p60 / 78, Example2.6 | EX: two-link spatial velocity has columns `(0,0,0,0,0,1)` and `(l₁cos θ₁,l₁sin θ₁,0,0,0,1)` | Source frame chain and constant offsets; differentiable joint angles | X41; concrete Ad; X40 | Verified: [I5](#implementation-evidence-i5); `Examples.twoLinkPose_factors`, `Examples.hasDerivAt_twoLinkPose`, `Examples.twoLinkPose_spatialVelocity` | This is the chapter-2 velocity example; agreement with independently defined chapter-3 FK remains K10's separate obligation |
| X46 theorem | p61 / 79, Lemma2.16 | SV: reversing frames gives `V_abᵇ=-V_baˢ` and `V_abᵇ=-Ad_(g_ba)V_baᵇ` | Inverse pose trajectories; differentiability | Inverse derivative; X31/X38 | Verified: [I4](#implementation-evidence-i4); `RigidTransform.hasDerivAt_toHomogeneous_inv`, `RigidTransform.bodyVelocity_eq_neg_spatialVelocity_inv`, `RigidTransform.bodyVelocity_eq_neg_adjoint_bodyVelocity_inv` | Preserve the ab/ba directions in both equations |

### Wrenches and reciprocal systems

| ID / kind | Source printed / PDF | Intended statement/module | Assumptions/conventions | Dependencies or missing bridge | Formal status | Statement divergence |
| --- | --- | --- | --- | --- | --- | --- |
| X47 definition | p61 / 79, Section5.1 | WR: wrench coordinates `(f,τ)` relative to a stated frame origin | Linear force first, moment second; same rigid body | Two-field structure over `Vec3`, componentwise vector space; pairing duality as the bridge to twists | Verified: [I4](#implementation-evidence-i4); `Wrench`, `Wrench.force`, `Wrench.torque`; [I8](#implementation-evidence-i8): `Wrench` is a two-field structure distinct from `Twist`, `Wrench.mk`, `Wrench.ext`, componentwise `AddCommGroup`/`Module ℝ` instances, `Wrench.finrank_eq_six` | Force components and moment reference point both matter |
| X48 definition | p61 / 79, work/pairing displays | WR: dual pairing `f·v+τ·ω`; work along a trajectory is its time integral | Compatible twist/wrench frames and units; integrability for work | Bilinear pairing and integration interface | Verified: [I6](#implementation-evidence-i6); `Wrench.intervalWork`, `Wrench.intervalWork_spatial_eq_body`, `Wrench.power_pointForce_eq_force_dot_deriv`, `Wrench.intervalWork_pointForce` | With velocities the pairing is instantaneous power; the book writes δW while integrating it against dt |
| X49 definition | p62 / 80, equivalent-wrench paragraph | WR: wrench equivalence means equality of pairing against every compatible instantaneous motion | Quantification over all twists, not just one trajectory | Nondegenerate pairing; X48 | Verified: [I4](#implementation-evidence-i4); `Wrench.Equivalent`, `Wrench.ext_pair`, `Wrench.equivalent_iff_eq` | Universal work equivalence can be related to this pointwise formulation only with temporal regularity/quantifier premises |
| X50 theorem | pp62-63 / 80-81, eqs2.65-2.67 | WR/AD: dual wrench transformation is transpose adjoint; equivalently `F_A=Ad_(g_AB⁻¹)ᵀF_B`, with force Rf and moment `p×Rf+Rτ` | Matching frame conversion and origin shift | X34-X36; dual map; CP signs | Verified: [I4](#implementation-evidence-i4); `Wrench.transform`, `Wrench.pair_transform`, `Wrench.transformMatrix_mulVec`, `Wrench.transformMatrix_eq_adjointMatrix_inv_transpose`, `Wrench.coordinates_transform` | Transformation includes shifting the moment origin, not merely rotating both vectors |
| X51 theorem | p63 / 81, pairing display after eq2.67 | WR: compatible spatial/body transformations preserve instantaneous power | `Vˢ=Ad_g Vᵇ`, `Fᵇ=Ad_gᵀFˢ` | X38/X48/X50; transpose pairing | Verified: [I4](#implementation-evidence-i4); `Wrench.pair_transform_adjoint` | Algebraic invariance is independent of physical model validation |
| X52 theorem | pp63-64 / 81-82, wrench-addition prose and Example2.7 | WR: transform a finite family to one frame/origin, then sum; result is the displayed net wrench | All wrenches on the same rigid body; compatible origins | X50; linearity of pairing and finite sums | Verified: [I4](#implementation-evidence-i4); `Wrench.net`, `Wrench.pair_net`, `Wrench.transform_net` | Does not establish grasp feasibility, contact persistence, or finite-force bounds |
| X53 definition | p64 / 82, eq2.68 | SC/WR: screw-generated wrench is `M(ω,-ω×q+hω)` for finite pitch and `(0,Mω)` for pure torque | Unit direction; explicit pure-torque branch | CP; X16/X47 | Verified: [I6](#implementation-evidence-i6); `Wrench.fromScrew`, `Wrench.pureCouple`, `Wrench.fromScrew_force`, `Wrench.fromScrew_torque`, `Wrench.pureCouple_force`, `Wrench.pureCouple_torque` | The algebraic moment includes an origin-dependent q×force term |
| X54 theorem | p65 / 83, Theorem2.17 (Poinsot) | SC/WR: every wrench admits a collinear force/couple representation | Separate zero wrench, pure torque, and nonzero force | X53; vector triple product; normalization | Verified: [I6](#implementation-evidence-i6); `Wrench.fromScrew_reconstruction`, `Wrench.pureCouple_reconstruction`, `Wrench.poinsot` | Source proof omits zero as trivial; formal target must cover it or state nonzero; representation is not unique |
| X55 definition | p65 / 83, eq2.69 | SC/WR: wrench pitch `(f·τ)/‖f‖²` for f≠0, infinite-pitch tag for pure torque | Nonzero denominator; zero wrench policy explicit | X47, Euclidean inner product | Verified: [I6](#implementation-evidence-i6); `Wrench.finitePitch_eq`, `Wrench.screwPitch`, `Wrench.screwPitch_of_force_ne_zero`, `Wrench.screwPitch_eq_stationary_iff`, `Wrench.screwPitch_eq_infinite_iff` | Zero pitch means no axial couple, not necessarily τ=0 about an arbitrary frame origin |
| X56 definition | p65 / 83, eq2.70 | SC/WR: wrench axis through `(f×τ)/‖f‖²` along f; pure-torque axis through origin along τ | f≠0, or f=0 and τ≠0 | X53-X55; affine line | Verified: [I6](#implementation-evidence-i6); `Wrench.finiteAxis`, `Wrench.mem_finiteAxis`, `Wrench.finiteAxis_direction_finrank`, `Wrench.coupleAxis`, `Wrench.mem_coupleAxis`, `Wrench.coupleAxis_direction_finrank`, `Wrench.screwAxis_eq_none_iff` | Zero wrench has no directed axis; choices along the axis are equivalent |
| X57 definition | p66 / 84, eq2.71 | SC/WR: magnitude is ‖f‖ when f≠0 and ‖τ‖ otherwise | Nonnegative magnitude with directional sign in axis | Euclidean norm; X47 | Verified: [I6](#implementation-evidence-i6); `Wrench.screwMagnitude`, `Wrench.screwMagnitude_of_force_eq_zero`, `Wrench.screwMagnitude_of_force_ne_zero`, `Wrench.screwMagnitude_nonneg`, `Wrench.screwMagnitude_smul` | This is not a common physical norm for mixed force/torque coordinates |
| X58 definition | p66 / 84, Definition2.3 | SC/WR: a twist and wrench are reciprocal iff their power pairing vanishes; induced reciprocal screws | Same reference frame and nondegenerate screw data if using geometric screws | X48, X18/X53 | Verified: [I6](#implementation-evidence-i6); `FiniteScrew`, `GeometricScrew`, `GeometricScrew.axis_finrank`, `GeometricScrew.toTwist_ne_zero`, `GeometricScrew.toWrench_ne_zero`, `GeometricScrew.Reciprocal`, `GeometricScrew.reciprocal_iff_coordinateProduct_zero`, `GeometricScrew.reciprocal_symm` | Zero power at one instant does not by itself establish a feasible finite motion |
| X59 definition | p67 / 85, unnumbered coordinate reciprocal product | SC: twist-coordinate reciprocal form `v₁·ω₂+v₂·ω₁` | Arbitrary real twists; symmetric bilinear form | X01; coordinate swap between twist and wrench roles | Verified: [I5](#implementation-evidence-i5); `Twist.swapWrench`, `Twist.reciprocalProduct_eq`, `Twist.reciprocalForm`, `Twist.reciprocalProduct_symm`, `Twist.reciprocalProduct_nondegenerate`; [I8](#implementation-evidence-i8): `Twist.swapWrench_force`, `Twist.swapWrench_torque`, `Twist.swapWrench_symm_apply`, the swap being an explicit named map between distinct types rather than `LinearEquiv.prodComm` | This form is nondegenerate but not a positive-definite Euclidean inner product |
| X60 theorem | pp66-67 / 84-85, eq2.72 and Proposition2.18 | SC: geometric reciprocal product equals the twist-wrench pairing, so reciprocity is its zero set | Finite pitches for printed proof; unit axes; signed-angle/common-normal convention | Scalar triple product; line geometry; X48/X53/X58 | Unverified (whole row); I6 checks `FiniteScrew.CommonNormal.isLeast_distance`, `pair_eq_reciprocalProduct`, and `GeometricScrew.reciprocal_finite_iff_geometricProduct_zero` only for a supplied positive-separation/nonparallel/signed-angle certificate; no certificate-existence or atan2 theorem | Printed d>0 and chosen common normal exclude intersecting/coincident cases; parallel cases and infinite pitches need separate definitions/proofs |
| X61 definition | pp68-69 / 86-87, screw-system and reciprocal-system prose | SC: system as a linear span of coordinate screws; reciprocal system as its annihilator | Explicit choice of twist/wrench identification; real finite dimension 6 | X59; Submodule; dual pairing | Verified: [I5](#implementation-evidence-i5); `Wrench.pairingEquiv`, `Twist.pairingEquiv`, `Reciprocal.wrenches`, `Reciprocal.twists`, `Reciprocal.mem_wrenches`, `Reciprocal.mem_twists` | Use spans/subspaces, not only finite lists with an assumed rank; geometric screw representatives have degeneracies |
| X62 theorem | p68 / 86, final linearity paragraph | SC: reciprocity against generators is equivalent to reciprocity against their span, and reciprocal systems are subspaces | Bilinear pairing; arbitrary finite generating set | X59/X61; linear algebra | Verified: [I5](#implementation-evidence-i5); `Reciprocal.mem_wrenches_span`, `Reciprocal.mem_twists_span` | No positive-definite metric is required; use the actual reciprocal bilinear form |
| X63 theorem | p69 / 87, Proposition2.19 | SC: dimension(system)+dimension(reciprocal system)=6 | Nondegenerate twist-wrench or reciprocal pairing; actual rank r | X59-X62; finite-dimensional annihilator/rank theorem | Verified: [I5](#implementation-evidence-i5); `Twist.finrank_eq_six`, `Reciprocal.wrenchesAnnihilatorEquiv`, `Reciprocal.twistsAnnihilatorEquiv`, `Reciprocal.finrank_add_finrank_wrenches`, `Reciprocal.finrank_add_finrank_twists`; [I8](#implementation-evidence-i8): `Wrench.finrank_eq_six`, now used by `Reciprocal.finrank_add_finrank_twists` | Frame-independent zero-power constraints are algebraic; interpreting the annihilator as physically feasible motion needs additional contact/dynamic premises |

### Gaps retained after this inventory

- These are selected obligations, not a full-book denominator and not independent
  Lean theorem counts. Multi-display propositions remain single source
  obligations where they state one relationship. The chapter-2 worked examples
  are selected as convention/derivative checks, not presumed substitutes for
  chapter-3 kinematic semantics.
- No bracket definition or theorem occurs on Chapter 2 pp39-69. I6 adds four
  separately sourced Appendix A rows below for the coordinate bracket, matrix
  bridge, Lie identities, and derived adjoint covariance. A manifold/tangent
  identification or general vector-field theory is not claimed.
- I6 supplies actual affine axes, independent finite/pure-translation screw
  motion, and explicit zero twist/wrench policies. The common-normal geometric
  reciprocal formula still requires a supplied certificate; its existence,
  atan2 identification, and unrestricted pair coverage remain open in X60.
- I6 defines a global noncomputable selected principal twist. Smoothness or
  uniqueness of that choice, global Euler coordinates, quaternion rotation
  bridges, manifold interfaces, full exercise coverage, typed frames/units,
  numerical refinement, physical-system fidelity, and user acceptance remain
  outside the checked scope.
- Physical language on pp68-69 about forces that cannot resist motion is not
  promoted to a dynamics theorem by a zero-power or annihilator calculation.
  Constraints, contact model, admissible forces, and solution regularity must be
  added at their later source obligations.

## Appendix A bracket obligations

I6 adds exactly four selected rows after bounded source inspection. They do not
exhaust Appendix A. The [preserved source inventory](../../docs/implogs/gates/E007/20261009T042046818411474Z/appendix-source-inventory.md)
records actual rendered pp407-408,410-411,415 and the coordinate-order caveat on
p417. The algebraic declarations do not construct a tangent bundle or establish
the general correspondence with left-invariant vector fields.

| ID / kind | Source printed / PDF | Intended statement/module | Assumptions/conventions | Dependencies or missing bridge | Formal status | Statement divergence |
| --- | --- | --- | --- | --- | --- | --- |
| L01 definition | p411 / 429, Example A.8 | LB: linear-first coordinate twist bracket `(ω₁×v₂−ω₂×v₁, ω₁×ω₂)` | Arbitrary real twists, including zero and nonunit axes | X01-X03; CP; HT | Verified: [I6](#implementation-evidence-i6); `Twist.bracket`, `Twist.bracket_linear`, `Twist.bracket_angular` | Uses explicit p411 ordering; p417 prose reverses the coordinates inconsistently |
| L02 bridge | pp410-411 / 428-429, Examples A.6-A.8 | LB: hat intertwines the coordinate bracket and actual matrix commutator; independent se(3) is closed | Independent block-defined carrier; reverse hat/vee conditions retained | X03; L01; associative matrix algebra | Verified: [I6](#implementation-evidence-i6); `Vec3.hat_cross`, `Twist.hat_bracket`, `se3_commutator_mem` | Includes the supporting so(3) hat-cross identity; no tangent-space equivalence claimed |
| L03 theorem | pp407-408 / 425-426, Lie algebra definition; p411 / 429, Example A.8 | LB: real bilinearity, alternating/skew symmetry, and Jacobi for the twist bracket | All real twists; actual coordinate bracket | L02; pinned matrix Lie identities | Verified: [I6](#implementation-evidence-i6); `Twist.bracketBilinear`, `Twist.bracket_self`, `Twist.bracket_antisymm`, `Twist.bracket_jacobi` | Right-nested cyclic Jacobi is equivalent to printed left-nested form via antisymmetry; no new global Lie instance |
| L04 bridge | p415 / 433, Example A.18; p411 / 429, Example A.8 | LB/AD: fixed rigid adjoint preserves the coordinate bracket | Any proper rigid transform and real twists; genuine conjugation | X35; L02; homogeneous inverse laws | Verified: [I6](#implementation-evidence-i6); `Twist.homogeneous_conjugate_commutator`, `Twist.adjoint_bracket`, `Twist.adjointEquiv_bracket`, `Twist.adjoint_bracket_eq_zero_iff` | Derived algebraic bridge, not a separately numbered proposition or arbitrary smooth-map pushforward theorem |

## First kinematic example and reusable obligations, Chapter 3

The future example is a planar two-revolute specialization of Example 3.1's SCARA
construction. Preserve zero-pose links along `+y`, set `l₀=θ₃=θ₄=0`, and write
lengths `a,b` and angles `q₁,q₂`. The target position is
`(-a sin q₁-b sin(q₁+q₂), a cos q₁+b cos(q₁+q₂), 0)` and orientation is
`Rz(q₁+q₂)`. This selected specialization is not a claim that MLS names that
exact two-link example. Real angles are a convenient coordinate lift; periodicity
must be established before identifying configurations with a torus.

| ID / kind | Source printed / PDF | Intended statement/module | Assumptions/conventions | Dependencies or missing bridge | Formal status | Statement divergence |
| --- | --- | --- | --- | --- | --- | --- |
| K01 definition | pp83-84 / 101-102, joint-space discussion | K/P: configuration domain and admissible subset | Revolute periodicity; optional explicit limits | Angle quotient or real-lift periodicity | Verified: [I7](#implementation-evidence-i7); `SerialChain` (fields `twist`, `toolRef`, `admissible`), `SerialChain.fk_add_int_mul_two_pi`, `SerialChain.fk_update_add_two_pi`, `Twist.IsRevoluteJoint.exp_add_int_mul_two_pi` | `ℝ²` coordinates are not a torus equivalence by definition. I7: real lift `Fin n → ℝ` with a periodicity theorem for revolute joints; no quotient or torus type; `admissible` is an explicit set (default all of `Fin n → ℝ`); joint type is a hypothesis predicate, not a field |
| K02 definition | p85 / 103, eq3.1, Fig3.2 | K/P: FK by adjacent-frame composition | Serial chain, base-to-tip order, tool offset | RT group/action, independently specified frames | Verified: [I7](#implementation-evidence-i7); `LinkFrameChain`, `LinkFrameChain.relative`, `LinkFrameChain.fk`; instance `Examples.planarTwoLinkFrames`, `Examples.planarTwoLinkFrames_fk` | First instance has two revolute joints; general chains later. I7: general `n`; the relative transform has the p85 form `exp(ζθ) g(0)` with `ζ` in the proximal link frame; the POE definition (eq3.3) is `SerialChain.fk` |
| K03 theorem | p87 / 105, revolute twist | K/P: reference joint twist `(-ω×q,ω)` | Unit axis, point on axis, base coordinates | P2 twist/exponential and axis semantics | Verified: [I7](#implementation-evidence-i7); `Twist.revolute`, `Twist.revolute_eq_fromScrew`, `Twist.revolute_axis_point`, `Twist.exp_revolute`, `Twist.exp_revolute_applyPoint`, `Twist.adjoint_revolute`, `Twist.IsRevoluteJoint` | Generalization needs independence of chosen point along axis. I7: definition is algebraic; the unit-axis premise is the explicit hypothesis of the exponential theorems; any point of `axisLine q ω` gives the same twist |
| K04 definition | p87 / 105, prismatic twist | K: reference prismatic twist `(v,0)` | Unit direction; displacement coordinate | Pure-translation exponential | Verified: [I7](#implementation-evidence-i7); `Twist.prismatic`, `Twist.IsPrismaticJoint`, `Twist.exp_prismatic`, `Twist.adjoint_prismatic` | Reusable target, not needed by two-revolute instance. I7: unit direction is the predicate `IsPrismaticJoint`; the exponential holds for every direction |
| K05 theorem | pp86-87 / 104-105, eqs3.2-3.3 | K/P: joint semantics equals ordered exponentials times reference pose | Constant reference twists; admissible angles | K02-K03, exponential conjugation/adjoint | Verified: [I7](#implementation-evidence-i7); sequential motion `SerialChain.moveJoint`, `runMoves`, `toolPose`, `moveJoint_linkPOE`, `toolPose_runMoves`, `toolPose_runMoves_perm`, `fk_single`; adjacent frames `LinkFrameChain.fk_eq_toSerialChain_fk`; instance `Examples.planarTwoLink_fk_eq_twoLinkPose` | Defining FK as POE and unfolding it is insufficient. I7: two independent semantics proved equal to POE (moves about current axes in any order; adjacent frames); arbitrary twists allowed; coordinate model only |
| K06 specification | pp87-89 / 105-107, Example 3.1 eq3.4, specialization | P: position as sum of rotated link displacements | Positive physical lengths, axes `+z`, zero links `+y` | R22, independent link/vector geometry | Verified: [I7](#implementation-evidence-i7); `Examples.planarTwoLinkPosition`, `Examples.planarTwoLinkPosition_eq` | New explicit geometric specification; positivity may be unused by algebra. I7: specification is the sum of the two `Rz`-rotated link vectors; `a, b` arbitrary reals, positivity unused |
| K07 theorem | p89 / 107, eq3.4, specialization | P: composed transform equals stated position and `Rz(q₁+q₂)` | `l₀=θ₃=θ₄=0`, `l₁=a`, `l₂=b` | K02, K06, angle addition | Verified: [I7](#implementation-evidence-i7); `Examples.planarTwoLink`, `Examples.planarTwoLink_fk`, `Examples.planarTwoLink_fk_rotation`, `Examples.planarTwoLink_fk_translation` | Specialized SCARA, not full four-joint example. I7: derived from the actual exponentials of the two revolute twists |
| K08 theorem | p84 / 102, revolute identification | P: FK is `2π`-periodic in each angle | Unrestricted ideal joints, real lift | K07, trigonometric periodicity | Verified: [I7](#implementation-evidence-i7); `Examples.planarTwoLink_fk_add_int_mul_two_pi` (from `SerialChain.fk_add_int_mul_two_pi`) | Explicit bridge to periodic configuration semantics. I7: integer multiples of `2π` in each angle; no torus equivalence type |
| K09 theorem | p115 / 133, differentiation; p118 / 136, final check | P/J: position derivative equals stated linear map on joint rates | Differentiable trajectory or Fréchet derivative | K07, derivative/trigonometric APIs | Verified: [I7](#implementation-evidence-i7); `Examples.hasDerivAt_planarTwoLink_translation` | Position Jacobian is not spatial twist Jacobian. I7: actual `HasDerivAt` along a joint trajectory with per-joint derivatives, not a Fréchet derivative in `θ` |
| K10 theorem | pp115-116 / 133-134, eqs3.51-3.54; p118 / 136, Example 3.8 | P/J: spatial Jacobian realizes `dot(g)g⁻¹` | `(v,ω)` order, same specialization | K05, adjoint, exponential/product derivative | Verified: [I7](#implementation-evidence-i7); `SerialChain.spatialJacobian`, `hasDerivAt_fk_toHomogeneous`, `spatialVelocity_fk`, `spatialJacobian_congr`, `spatialJacobianMatrix_mulVec`; instance `Examples.planarTwoLink_spatialJacobian_zero`, `Examples.planarTwoLink_spatialJacobian_one`, `Examples.planarTwoLink_spatialVelocity`, `Examples.planarTwoLink_spatialVelocity_eq_twoLinkPose` | Columns `(0,0,0,0,0,1)` and `(a cos q₁,a sin q₁,0,0,0,1)` need derivative proof. I7: general `n`, arbitrary (not only unit) twists; columns as `Fin n → Twist`, matrix view through `Twist.coordinates` |
| K11 theorem | p117 / 135, eq3.56 | J/P: `Jˢ=Ad_g Jᵇ` | Compatible spatial/body conventions | Velocity/adjoint relations, K10 | Verified: [I7](#implementation-evidence-i7); `SerialChain.bodyJacobian`, `spatialJacobian_eq_adjoint_bodyJacobian`, `bodyJacobian_eq_adjoint_inv_spatialJacobian`, `bodyVelocity_fk` | No arbitrary 6D Euclidean norm invariance follows. I7: column-wise identity for every real joint vector |
| K12 theorem | p117 / 135, point velocity; p118 / 136, final check | P/J: twist velocity at tool origin equals position derivative | Spatial point is `p(q)`, body origin is zero | K09-K10, twist action | Verified: [I7](#implementation-evidence-i7); `SerialChain.hasDerivAt_fk_translation`, `hasDerivAt_fk_translation_body`; planar check `Examples.planarTwoLink_point_velocity`, `Examples.hasDerivAt_planarTwoLink_translation_of_jacobian` | Must include `ω×p`; translational twist part alone is not `dot(p)`. I7: derivative is `ωˢ × p + vˢ` (spatial) and `R vᵇ` (body) |
| K13 theorem | p121 / 139, eqs3.59-3.60 | J/P: force pullback preserves instantaneous power | Matched wrench/Jacobian frames, arbitrary joint rates | Dual pairing, transpose identity, K10/K11 | Unverified | Algebraic identity separate from frictionless physical-work premise. I7: deferred to a later brief (Wrench type change in progress); no Wrench module imported by I7 |
| K14 definition | p95 / 113, eq3.11 | W: complete workspace is FK image | Explicit admissible domain `Q` | FK, set image | Verified: [I7](#implementation-evidence-i7); `SerialChain.completeWorkspace`, `toolRef_mem_completeWorkspace`, `completeWorkspace_mono` | Pose reachability, not path or dynamic feasibility. I7: `Q` is an explicit argument |
| K15 definition | p95 / 113, eq3.12 | W/P: reachable workspace is position image | Same domain `Q` | Position projection, set image | Verified: [I7](#implementation-evidence-i7); `SerialChain.reachableWorkspace`, `reachableWorkspace_eq_image`, `reachableWorkspace_mono`, `toolRef_translation_mem_reachableWorkspace`, `reachableWorkspace_of_zero_joints` | Does not quantify over all orientations. I7: `Q` is an explicit argument |
| K16 definition | p95 / 113, eq3.13 | W: dextrous workspace uses `∀R,∃q` realizing `(p,R)` | Orientations range over `SO(3)` | Pose FK, explicit quantifier order | Verified: [I7](#implementation-evidence-i7); `SerialChain.dextrousWorkspace`, `mem_dextrousWorkspace_iff`, `dextrousWorkspace_subset_reachableWorkspace`, `dextrousWorkspace_mono`, `dextrousWorkspace_of_zero_joints`; planar `Examples.planarTwoLink_dextrousWorkspace_eq_empty`, `Examples.planarTwoLink_reachableWorkspace_nonempty` | Planar pilot cannot realize arbitrary 3D orientations; name any planar variant separately. I7: `∀R,∃θ∈Q` as printed; the planar pilot's 3D dextrous workspace is proved empty; no planar-orientation variant is defined; no nonempty-dextrous instance is exhibited |

An annulus theorem for positive lengths and unrestricted joints is a useful next
derived target, not a quoted theorem from the inspected pages. Its eventual row
must cover both inclusions, zero radius, and equal lengths. Joint limits,
collision avoidance, continuous IK selection, and motion feasibility are separate.

## Broader backlog: denominator not yet established

These packages retain comprehensive library scope. They are chapter-level
backlog, **not counted theorem rows**. The P2 row links the fresh statement-level inventory above; the other package
ranges are carried from the [roadmap](lean-library-roadmap.md) and are not a new
statement-level audit of those chapters.

| Package | Source/dependencies | Selected coverage | Remaining inventory and exit evidence |
| --- | --- | --- | --- |
| P0 conventions/inventory | All branches | This ledger and coordinate convention | Expand remainder with stable source rows; separate mathematical, numerical, physical claims |
| P1 rigid transforms | Ch2 pp23-38, Appendix A | Applicable R01-R11, T01-T15 | Check selected claims, homogeneous equivalence, orientation; evaluate frame indices; exercises still un-inventoried |
| P2 twists/exponentials/duality | Ch2 pp27-30,39-69, Appendix A; P1 | R07-R21 and new X01-X63; optional R22-R28 | R13-R18 checked in I3; all X rows Unverified; bracket source inventory, degenerate geometry, and local logarithms remain open |
| P3 kinematics | Ch3 pp81-154; P1/P2 | K01-K16 only | General chains, IK branches, rank/singularities, closed chains, other examples un-inventoried |
| P4 energy/dynamics | Ch4 pp155-178; P2/P3 | None | Inertia, energies, mass/Coriolis structure, Euler-Lagrange/Newton-Euler; strict positivity needs nondegeneracy |
| P5 trajectories/control | Ch4 pp179-207; P4/analysis | None | Solution regularity, Lyapunov, exact-model control; resolve Proposition 4.9 gravity-term caution |
| P6 grasp/contact | Ch5 pp211-264; P2/P3 branch | None | Contact cones, grasp map, force closure, manipulation/rolling; rank, force bounds, smoothness/curvature |
| P7 constraints/composition | Ch6 pp265-316; P4/P6 | None | Pfaffian constraints, ideal reactions, constrained energy, tendon feasibility, attachment/control composition |
| P8 nonholonomic analysis | Ch7 pp317-354; Appendix A/analysis | None | Flows, distributions, brackets, Frobenius/Chow and examples; signed-control/domain assumptions |
| P9 steering | Ch8 pp355-394; P8 | None | Chained forms, sinusoidal constructions, coordinate domains, exact/approximate steering, error bounds |
| P10 computation/refinement | Appendix B pp435-439; prior specs | None | Exact evaluator or checked-certificate interface, approximation/refinement; external floats not covered by real proofs |

Relevant Appendix A foundations are selected where used. Chapters 1 and 9 remain
contextual. Exercises are selected for reusable results; covering every exercise
is not presumed. Design, composition, control, planning, learning, and software
verification remain potential users of shared foundations. Calendar estimates
and full-book completion fractions remain unsupported.

## Implementation evidence I1

The 21 rows marked Verified I1 refer to their named declarations in
[the rigid-transform core](../../RoboLean/Geometry/RigidTransform.lean) and
[the homogeneous bridge](../../RoboLean/Geometry/Homogeneous.lean), checked by
[the combined build and audit](../../docs/implogs/gates/E001/20261009T004447Z/commands.json).
The [build output](../../docs/implogs/gates/E001/20261009T004447Z/lake-build.stdout)
records `lake build` exit 0 under
[Lean 4.34.1](../../docs/implogs/gates/E001/20261009T004447Z/lean-version.stdout)
and the pinned mathlib 4.34.1 dependency. The
[explicit axiom audit](../../docs/implogs/gates/E001/20261009T004447Z/axioms.stdout)
records 67 requested declarations from the core, bridge, examples, and smoke
module, each depending only on `propext`, `Classical.choice`, and `Quot.sound`.
The [source hashes](../../docs/implogs/gates/E001/20261009T004447Z/source-hashes.json)
identify the checked artifacts. The audit's 67 declarations are not the 59 source
obligations and are not a book-coverage metric.

For definition rows, the evidence is the elaborated definition and inspected
coordinate expression; this does not count as a new mathematical theorem. R03
reuses mathlib's group instance on the alias `Rotation`; T12's new group instance
is `RoboLean.RigidTransform.instGroup`, explicitly included in the axiom audit.
R04 uses `Rotation.inv_val`; T11 also uses
`RigidTransform.inv_translation_coordinates`. T15 uses both
`RigidTransform.homogeneousEquiv` and `RigidTransform.toHomogeneousHom`; there is
no claim that a target subgroup instance was built.

These checks concern the displayed statements and their mathematical coordinate
model. At I1, R09 and T14 remained Unverified: `rotation_det` proves determinant
one, not the MLS cross-product equation. The later I2 gate below checks that
equation directly. No arbitrary-map characterization, typed
frame correctness, numerical refinement, physical-system validity, Chapter 3
result, or user acceptance is inferred.

## Implementation evidence I2

The six rows marked Verified I2 are R07, R08, R09, R10, R12, and T14: one
definition, four theorem obligations, and one representation bridge. The
[default build and consolidated audit](../../docs/implogs/gates/E003/20261009T015317Z/summary.json)
checked [CrossProduct.lean](../../RoboLean/Geometry/CrossProduct.lean) and
[Hat.lean](../../RoboLean/Geometry/Hat.lean), integrated through the root imports.
[Commands and exits](../../docs/implogs/gates/E003/20261009T015317Z/commands.json) record
`lake build` and the explicit Lean audit exiting zero under Lean 4.34.1 and
pinned Mathlib 4.34.1. The [actual audit output](../../docs/implogs/gates/E003/20261009T015317Z/axioms.stdout)
contains all 85 requested declarations: the prior 67 plus all 18 new public
declarations, each depending only on `propext`, `Classical.choice`, and
`Quot.sound`. These are declaration counts, not independent theorem counts.

The [source hashes](../../docs/implogs/gates/E003/20261009T015317Z/source-hashes.json) and
[post-check hashes](../../docs/implogs/gates/E003/20261009T015317Z/source-hashes-after.json) agree for 25
named artifacts, including seven project Lean files, build/toolchain files,
relevant pinned Mathlib sources, MLS.pdf, and the audit source. The
[review](../../docs/implogs/gates/E003/20261009T015317Z/review.md) maps the actual statements to rendered
MLS printed pp.26–28 and 37–38. A separately checked exact `e_x × e_y = e_z`
witness is retained with the [author audit](../../docs/implogs/gates/E003/20261009T015317Z/provenance/robo-cross-audit.stdout).

R12 is an actual real linear equivalence to the independently defined
`skewAdjoint` matrix type, with `mem_skewMatrix3_iff` identifying its elements by
`Aᵀ = -A`. `hat_vee` retains that hypothesis; `vee_hat` covers every vector.
R09 explicitly uses determinant one, and T14 acts on free vectors. No unit-vector
restriction, translation-dependent vector action, or arbitrary-matrix inverse
claim is introduced.

**Unverified at I2 (historical boundary):** hat square/cube identities, exponentials, the converse
characterization of arbitrary rigid maps, frame/unit and separate point/vector
types, selected kinematics, numerical refinement, physical-model fidelity, and
user acceptance. No full-book coverage claim follows from the selected counts.

## Implementation evidence I3

**Verified - named formal statements:** [combined commands](../../docs/implogs/gates/E004/20261009T022521Z/commands.json)
record the default build and consolidated axiom audit exiting zero with
[Lean 4.34.1](../../docs/implogs/gates/E004/20261009T022521Z/lean-version.stdout) and pinned Mathlib 4.34.1. The actual
[build output](../../docs/implogs/gates/E004/20261009T022521Z/lake-build.stdout) and
[audit output](../../docs/implogs/gates/E004/20261009T022521Z/axioms.stdout) cover 115 requested/reported declarations:
the prior 85 plus 30 public declarations from
[HatPowers](../../RoboLean/Geometry/HatPowers.lean),
[RotationExp](../../RoboLean/Geometry/RotationExp.lean),
[Rodrigues](../../RoboLean/Geometry/Rodrigues.lean), and
[exponential examples](../../RoboLean/Examples/RotationExp.lean).
Only `propext`, `Classical.choice`, and `Quot.sound` occur. The
[summary](../../docs/implogs/gates/E004/20261009T022521Z/summary.json) records 44 unchanged named source/toolchain,
manifest, pinned-API, PDF, audit, and harness hashes. These are declaration and
artifact counts, not independent theorem or source-obligation counts.

R13/R14 use `Vec3.hat_sq` and `hat_cube` for arbitrary Euclidean vectors.
R15 uses the actual point-action derivative `Rotation.hasDerivAt_exp_act`
together with `exp_zero_act`. R16/R17 use actual `NormedSpace.exp` equalities,
with unit, nonzero, and zero-axis cases stated separately. R18 proves full
`SO(3)` membership for every real skew matrix, including determinant +1, and
`expSkew` supplies the real parameter. The
[independent source/statement review](../../docs/implogs/gates/E004/20261009T022521Z/source-statement-review.md)
compares those declarations with rendered MLS pp27-31 and records the exact
hypotheses and proof limits.

The four exact examples connect exp(+z,π/2) to the previously defined
quarter-turn matrix, check e_x maps to e_y and e_z is fixed, and show
exp(2e_z,π/4) is the same quarter turn. They add no R22 coverage. This increment
adds six theorem obligations, R13-R18, to the prior 27 covered obligations.
Separately, source inventory adds 63 Unverified X rows to the original 59 rows:
33 Verified and 89 Unverified out of 122 selected obligations. The denominator
expansion is newly recorded backlog, not a drop in proof coverage or a whole-book
percentage.

**Unverified:** R19-R28, all X01-X63 and K01-K16, arbitrary-map rigid-motion
characterization, ODE uniqueness, local/global logarithm selection, typed frames
and units, numerical refinement, physical fidelity, and user acceptance.

## Implementation evidence I4

**Verified - named formal statements:** the [combined commands](../../docs/implogs/gates/E005/20261009T032143837813448Z/commands.json)
record the default build, environment inventory, and axiom audit exiting zero.
The actual [Lean version](../../docs/implogs/gates/E005/20261009T032143837813448Z/lean-version.stdout) is 4.34.1, with pinned
Mathlib 4.34.1. The [build output](../../docs/implogs/gates/E005/20261009T032143837813448Z/lake-build.stdout),
[raw axiom output](../../docs/implogs/gates/E005/20261009T032143837813448Z/axioms.stdout), and
[declaration inventory](../../docs/implogs/gates/E005/20261009T032143837813448Z/declaration-inventory.json) identify 355 audited
declarations: the previous 115 plus 240 new declarations (225 public and 15
private). Only `propext`, `Classical.choice`, and `Quot.sound` occur. These
counts include definitions and supporting helpers; they are not independent
robotics theorem counts. One nonblocking `unnecessarySeqFocus` style warning
remains in `Examples/Twist.lean`.

The [independent evidence review](../../docs/implogs/gates/E005/20261009T032143837813448Z/independent-evidence-review.json)
checks the actual ordered output, source signatures, generated auxiliaries,
root imports, and final hashes. The
[independent source/statement review](../../docs/implogs/gates/E005/20261009T032143837813448Z/source-statement-review.md)
compares the exact declarations and assumptions with twenty rendered MLS pages:
printed pp39-44 and 51-64. The
[exact obligation mapping](../../docs/implogs/gates/E005/20261009T032143837813448Z/ledger-proposal.json) records each declaration,
source equation, and full/partial scope. That reviewer independently found all
123 mapped declaration names in the raw audit and matched 18 final source/root,
toolchain/manifest, and PDF hashes with the gate. The
[gate summary](../../docs/implogs/gates/E005/20261009T032143837813448Z/summary.json) retains the broader run checks and limits.

I4 adds 36 fully covered selected rows:
X01-X11, X13, X26-X38, X40-X44, X46-X47, and X49-X52. With the previous 33,
there are 69 Verified rows out of the unchanged selected inventory of 122:
15 definitions, two structures, 43 theorem obligations, and nine bridges.
The other 53 remain Unverified as whole rows. Historical I1-I3 records above
retain their then-current counts and evidence states.

The checked interfaces distinguish the independent `se(3)` carrier from twist
coordinates, and genuine matrix exponentials from selected closed forms.
`Twist.exp_hat_of_angular_norm_eq_one` retains the unit-axis premise;
`exp_normalize_angular` rescales both linear and angular components, with a
separate zero-angular case. X13 proves the actual translation coefficient is
invertible on `0<θ<2π` for a unit axis and records determinant zero at a full
turn. X12 and R19 exponential-surjectivity obligations remain Unverified.

Velocity definitions require actual `HasDerivAt` evidence. The checked point,
spatial/body, composition, fixed-frame, and inverse laws preserve the frame
conventions and distinguish body-expressed physical velocity from a derivative
of fixed body coordinates. For arbitrary differentiable θ(t), X40 gives
`Vˢ=θ̇ξ` and `Vᵇ=θ̇ Ad_(g₀⁻¹)ξ`; a constant twist alone does not imply constant
velocity. Wrench transfer includes the moment-origin shift and agrees with the
literal transpose of the inverse adjoint; the independently defined pairing is
preserved. Finite wrench families are transferred to a common frame before
summing.

**Unverified - whole rows with checked partial results:** X39 has the exact
`l0=0, l1=3, l2=5, θ(t)=2t` example at t=0 in
[Examples/Velocity](../../RoboLean/Examples/Velocity.lean): the actual body-origin
velocity is `(-10,0,0)`, spatial linear twist `(6,0,0)`, body linear twist
`(-10,0,0)`, and both angular parts `(0,0,2)`. The full symbolic X39 row is not
closed by that instance. X48 has `Wrench.pair`, its bilinear interface, and
instantaneous-power identities; no time integral or integrability theorem is
claimed. The [twist](../../RoboLean/Examples/Twist.lean) and
[wrench examples](../../RoboLean/Examples/Wrench.lean) also check ordering,
nonunit scaling, origin shifts, and the explicit 91-versus-112 pairing control.

**Unverified:** the remaining source rows, rotation/rigid exponential
surjectivity, broader screw/reciprocal-system semantics, Appendix A bracket
inventory, general chapter-3 kinematic semantics, ODE uniqueness, global
logarithm selection, typed frames/units, numerical refinement, physical fidelity,
and user acceptance. A proof check establishes the stated mathematical
relation under its assumptions, not the fidelity of a physical robot model.

## Implementation evidence I5

**Verified - named formal statements:** the [combined commands](../../docs/implogs/gates/E006/20261009T034628198810517Z/commands.json)
record the default build, environment inventory, and combined axiom audit
exiting zero for the frozen nine-module snapshot. The actual
[Lean version](../../docs/implogs/gates/E006/20261009T034628198810517Z/lean-version.stdout) is 4.34.1 with the unchanged pinned
Mathlib/toolchain. The [build output](../../docs/implogs/gates/E006/20261009T034628198810517Z/lake-build.stdout) records two
nonblocking style warnings, in the earlier twist examples and the new
RotationPlane helper. The [raw audit](../../docs/implogs/gates/E006/20261009T034628198810517Z/axioms.stdout) contains exactly
501 ordered declarations: the prior 355 plus 146 new explicit declarations.
Only `propext`, `Classical.choice`, and `Quot.sound` occur; two constructor rows
have empty axiom sets. `ScrewPitch` and its three authored constructors are
included. These counts are declarations, not independent mathematical theorems.

The [independent evidence readback](../../docs/implogs/gates/E006/20261009T034628198810517Z/independent-evidence-review.json)
checks declaration provenance, generated auxiliaries, and all 92 recorded
hash inputs. The [source/statement review](../../docs/implogs/gates/E006/20261009T034628198810517Z/source-statement-review.md)
compares the nine actual files with rendered source pages and independently
matches all 72 names in the [exact row mapping](../../docs/implogs/gates/E006/20261009T034628198810517Z/ledger-proposal.json)
to the raw audit, together with 13 current module/root/toolchain/manifest/PDF
hashes. The [summary](../../docs/implogs/gates/E006/20261009T034628198810517Z/summary.json) records the exact snapshot scope.
Later queued modules are excluded from this evidence claim.

I5 adds 15 fully covered selected rows: R19-R22, X12, X19, X21-X23, X39,
X45, X59, and X61-X63. There are now 84 Verified rows out of the unchanged
122: 21 definitions, two structures, 52 theorem obligations, and nine bridges.
The other 38 remain Unverified as whole rows. Historical I1-I4 sections retain
their original counts and then-current evidence states.

[RotationAxis](../../RoboLean/Geometry/RotationAxis.lean) and
[RotationPlane](../../RoboLean/Geometry/RotationPlane.lean) supply an actual unit
fixed axis and a Euclidean adapted orthonormal basis. The
[rotation existence proof](../../RoboLean/Geometry/RotationSurjectivity.lean)
uses a planar complex argument, including identity and half turns without a
sine denominator; it gives both a unit-axis exponential and an angle in
`[0,2π)`. [RotationLog](../../RoboLean/Geometry/RotationLog.lean) proves the
trace-based principal angle and generic skew-entry axis reconstruction under
`sin(principalAngle R) ≠ 0`, with separate half-turn projector existence.
[ElementaryRotations](../../RoboLean/Geometry/ElementaryRotations.lean) checks
all three displayed matrix families for every real angle, beyond single
quarter-turn examples. Euler inverse charts and quaternion rows are separate.

[TwistSurjectivity](../../RoboLean/Geometry/TwistSurjectivity.lean) proves every
rigid transform is an actual twist exponential, with a pure-translation branch
and a positive principal-angle branch using the previously checked translation
coefficient inverse. It also rescales the entire twist to parameter one.
These are existence results, without a unique or smooth logarithm.
[TwistScrew](../../RoboLean/Geometry/TwistScrew.lean) checks finite pitch,
nonnegative magnitude, the two unit-twist branches, and axis-point shift
independence of both the generator and actual exponential. Zero receives an
explicit stationary pitch tag rather than being silently identified with a
nonzero infinite-pitch translation. Norm magnitude scales by `abs(c)`; the
scalar sign is not a norm.

The [symbolic velocity examples](../../RoboLean/Examples/PlanarVelocity.lean)
now cover X39 for arbitrary real fixed offsets and differentiable angle, with
an independent full source-matrix equality and actual derivative. X45 similarly
uses the explicit two-frame source chain and both actual joint derivatives to
obtain the printed spatial columns. This does not establish K10's independent
Chapter-3 forward-kinematics semantics.
[Reciprocal](../../RoboLean/Geometry/Reciprocal.lean) checks the explicit swapped
coordinate reciprocal form, actual annihilator subspaces, generator/span
criteria, double reciprocity, and dimension sum six. The pairing is
nondegenerate, not positive definite; no contact feasibility follows.

**Unverified - whole rows with bounded partial evidence:** X20 has only the
perpendicular finite-axis point and its algebraic reconstruction/invariance in
this snapshot. X58 has coordinate zero-power reciprocity and frame covariance,
without induced geometric screw representatives. X48 retains I4's instantaneous
pairing/bilinearity evidence without a work-integral theorem. Later axis,
geometric reciprocity, work, Euler, and bracket files are not part of I5.
No Appendix A rows are added here; its separately prepared source inventory
awaits a corresponding frozen proof/source gate.

**Unverified:** all remaining rows, full geometric screw/Chasles semantics,
time-integrated work, unrestricted or smooth logarithm selection, global Euler
charts, quaternion interfaces, independent chapter-3 kinematic semantics,
physical fidelity, numerical refinement, and user acceptance. Specific later
results must be recorded against their own source and evidence before these
statuses change.

## Implementation evidence I6

**Verified - named formal statements:** the [final combined commands](../../docs/implogs/gates/E007/20261009T042046818411474Z/commands.json)
record default build, environment inventory, and combined axiom audit exiting
zero for all 21 landing modules. The actual
[Lean version](../../docs/implogs/gates/E007/20261009T042046818411474Z/lean-version.stdout) is 4.34.1 with unchanged pinned
Mathlib/toolchain. The [raw audit](../../docs/implogs/gates/E007/20261009T042046818411474Z/axioms.stdout) has exactly 864 ordered
declarations: the prior 501 plus 363 new explicit declarations, comprising
345 public and 18 private declarations. There are 861 rows with only
`propext`, `Classical.choice`, and `Quot.sound`, and three empty constructor
sets. These counts include definitions and supporting helpers; they are not
independent mathematical theorem counts. The [build output](../../docs/implogs/gates/E007/20261009T042046818411474Z/lake-build.stdout)
retains nonblocking style/unused-tactic warnings in Examples/Twist,
RotationPlane, and TwistScrewMotion.

The [independent evidence review](../../docs/implogs/gates/E007/20261009T042046818411474Z/independent-evidence-review.json)
checks actual declaration provenance, authored constructors, structure fields
and generated auxiliaries, and all 121 recorded input/audit hashes. The
[independent source review](../../docs/implogs/gates/E007/20261009T042046818411474Z/source-statement-review.md) compares all 21
actual files with rendered formulas, matches every one of the 111 names in the
[exact ledger mapping](../../docs/implogs/gates/E007/20261009T042046818411474Z/ledger-proposal.json) to the raw output, and binds
26 current source/root/toolchain/manifest/PDF/pinned-group-API hashes. The
[summary](../../docs/implogs/gates/E007/20261009T042046818411474Z/summary.json) names the fixed gate scope. No Kinematics files
or uncompiled candidate are included.

I6 adds 19 full results among the original 122 rows: R23-R26, X14-X18, X20,
X24-X25, X48, and X53-X58. It also adds and checks four source-inventoried
Appendix rows L01-L04. The current selected inventory therefore has 126 IDs,
with 107 Verified in full (30 definitions, three structures, 63 theorem
obligations, and 11 bridges). The other 19 remain Unverified: R27-R28, X60 in
full, and K01-K16. The denominator grew because of four explicit Appendix
obligations, not a new estimate of whole-book coverage. I1-I5 historical
sections retain their original counts and evidence states.

[Angular parameter identities](../../RoboLean/Geometry/RotationParameters.lean)
and [axis uniqueness](../../RoboLean/Geometry/RotationAxisUniqueness.lean)
separate the principal interior, half-turn sign ambiguity, and zero-angle
ambiguity. [TwistLog](../../RoboLean/Geometry/TwistLog.lean) defines a global
noncomputable selected principal twist and proves its actual exponential
reconstructs every pose. The inverse translation equation is unique only for
a fixed unit axis and `0<θ<2π`; the chosen global twist is not asserted unique,
smooth, or executable numerically. The implementation uses the actual matrix
inverse, not Appendix p414's printed sine-denominator expression at its
singular cases.

[EulerAngles](../../RoboLean/Geometry/EulerAngles.lean) proves the independent
ZYZ matrix formula and a generic inverse with explicit complex-argument
`atan2` branches and positive radial quantity. The chosen middle angle lies
strictly in `(0,π)`; both zero-sine endpoints and global charts are excluded.
[UnitQuaternion](../../RoboLean/Geometry/UnitQuaternion.lean) proves the
scalar/vector product for arbitrary quaternions and identifies the reused
unitary group with the independent norm-one condition. Zero is excluded from
the group. Quaternion-to-rotation, half-angle rotation equivalence, and the
multiplication-preserving rotation map remain absent (R27-R28).

[TwistScrewMotion](../../RoboLean/Geometry/TwistScrewMotion.lean) compares an
independent geometric finite/pure-translation/stationary carrier with actual
exponentials. It includes the absolute-pose example under `cos θ≠1`, the
all-angle relative-pose example, and finite-axis point motion.
[Chasles](../../RoboLean/Geometry/Chasles.lean) proves every proper displacement
satisfies an independent geometric point-action predicate.
[ScrewAxis](../../RoboLean/Geometry/ScrewAxis.lean) supplies genuine finite and
pure-translation affine lines, their rank-one directions, a parallel-axis
family, and zero=None. The
[normalization](../../RoboLean/Geometry/NormalizedTwist.lean),
[twist frame](../../RoboLean/Geometry/TwistScrewInvariants.lean), and
[geometric conjugation](../../RoboLean/Geometry/ScrewConjugation.lean) bridges
retain signed parameters and distinguish unoriented line sets from directed
coordinates; no extra source obligations are counted for these helpers.

[WrenchScrew](../../RoboLean/Geometry/WrenchScrew.lean) proves normalized
Poinsot reconstruction with zero/pure-couple/nonzero-force cases and actual
affine axes. [WrenchWork](../../RoboLean/Geometry/WrenchWork.lean) now includes
the actual time integral with explicit interval integrability and actual
pose-derived point-velocity identities. The
[wrench frame laws](../../RoboLean/Geometry/WrenchFrameInvariants.lean) separate
finite-axis point covariance from the canonical pure-couple origin axis,
which rotates and needs a translation-in-span premise for point covariance.

**Unverified - X60 in full:**
[WrenchReciprocityGeometry](../../RoboLean/Geometry/WrenchReciprocityGeometry.lean)
adds actual nonzero finite/infinite geometric representatives and induced
reciprocity (X58). Its common-normal certificate carries positive separation,
nonparallel unit axes, perpendicular unit normal, selected point displacement,
and signed sine/cosine equations. The implementation proves the separation is
an attained minimum and proves the geometric reciprocal formula for that
certificate. Existence of certificates for arbitrary source screw pairs,
`atan2` identification, and parallel/intersecting/infinite-pitch geometric
formula coverage are not supplied. The whole X60 row remains Unverified;
its checked conditional result is recorded explicitly rather than promoted.

L01-L04 cover the named real coordinate bracket, independent hat/commutator
bridge and se(3) closure, Lie identities, and derived fixed adjoint covariance.
They do not claim a global Lie instance for twists, tangent/manifold
identification, or unrestricted smooth-map pushforward. The
[bounded Appendix inventory](../../docs/implogs/gates/E007/20261009T042046818411474Z/appendix-source-inventory.md) records
source p411's linear-first convention and the conflicting p417 prose.
The four independent [screw](../../RoboLean/Examples/Screw.lean),
[wrench](../../RoboLean/Examples/WrenchScrew.lean),
[reciprocal](../../RoboLean/Examples/Reciprocal.lean), and
[rotation-log](../../RoboLean/Examples/RotationLog.lean) example files check
literal signs, norms, degeneracies, pairing controls, and endpoint behavior.
They are exact theorem witnesses, not numerical experiments or physical tests.

**Unverified:** R27-R28, full X60, every K01-K16 statement, smooth/unique
logarithm selection, global Euler coordinates, manifold-level identification,
physical fidelity, numerical refinement, and user acceptance. No Chapter-3
kinematics file was created; source preparation or Chapter-2 velocity examples
do not close those obligations. The user-requested landing stops new research.

## Implementation evidence I7

Recorded 2026-10-09 UTC for [E009](../../docs/implogs/E009-serial-chain-kinematics.md),
the first Chapter 3 tranche. New modules:
[SerialChain](../../RoboLean/Kinematics/SerialChain.lean),
[Jacobian](../../RoboLean/Kinematics/Jacobian.lean),
[Workspace](../../RoboLean/Kinematics/Workspace.lean) and
[PlanarTwoLink](../../RoboLean/Examples/PlanarTwoLink.lean). Sources were read this
increment at printed pp. 83–89, 95 and 115–122
([text extracts](../../docs/implogs/gates/E009/20261009T084633Z/source/)), with
pp. 87, 88 and 116–118 also inspected as [rendered images](../../docs/implogs/gates/E009/20261009T091048Z/render/).

**Verified - shadow-tree elaboration:** with the pinned Lean 4.34.1 binary and the
built Mathlib v4.34.1 and library oleans on `LEAN_PATH`, each of the four files
elaborated with exit 0 and no warning, in dependency order
([checks](../../docs/implogs/gates/E009/20261009T091048Z/), e.g. [SerialChain](../../docs/implogs/gates/E009/20261009T091048Z/check-SerialChain.out),
[PlanarTwoLink](../../docs/implogs/gates/E009/20261009T091048Z/check-PlanarTwoLink.out)). The
[axiom audit](../../docs/implogs/gates/E009/20261009T091048Z/axioms.out) prints 101 ordered rows for the 101 public declarations
listed in [public-decls](../../docs/implogs/gates/E009/20261009T091048Z/public-decls.txt) (79 in the three Kinematics modules,
22 in the example, structures and their constructors included); every row has
exactly `propext`, `Classical.choice` and `Quot.sound`
([verifier output](../../docs/implogs/gates/E009/20261009T091048Z/axioms-verify.txt)). No `sorry`, `axiom` or `opaque` occurs
([grep](../../docs/implogs/gates/E009/20261009T091048Z/forbidden-grep.txt)), and the project import closure contains no
Wrench-family module ([closure](../../docs/implogs/gates/E009/20261009T091048Z/import-closure.txt)). Hypotheses whose
satisfiability is not immediate are instantiated in
[Instances.lean](../../docs/implogs/gates/E009/20261009T091048Z/Instances.lean) (exit 0, [output](../../docs/implogs/gates/E009/20261009T091048Z/instances.out)).
Limits: this is not the integrated `lake build` of the root import list, which is
root's landing check; the checks used the oleans built at the start of the
increment, while three upstream sources in the import closure (Geometry/RigidTransform,
RotationPlane, TwistScrewMotion) carried uncommitted docstring and tactic edits by
another agent that were not rebuilt. Counts include definitions, structures and
constructors; they are not independent theorem counts.

I7 marks fifteen rows Verified in full: K01–K12 and K14–K16 (six definitions K01,
K02, K04, K14, K15, K16; eight theorem obligations K03, K05, K07–K12; one
specification K06). With the 107 rows of I6 this gives 122 of the 126 selected IDs
Verified in full; the remaining four are R27, R28, X60 (partial) and K13. K13
(force pullback, p121, eqs3.59–3.60) was excluded from this tranche because the
wrench carrier is being changed concurrently. These are selected-item counts, not
a whole-book percentage, and the "Scope and counting" section above still states
the I6 counts.

K05 is discharged by two semantics that do not use the product formula:
`SerialChain.toolPose_runMoves_perm` (moving each joint once, in any order, about
its current axis carried by the proximal link, pp86–87) and
`LinkFrameChain.fk_eq_toSerialChain_fk` (adjacent link frames, eq3.1). Joint
coordinates are a real lift with the periodicity theorem
`SerialChain.fk_add_int_mul_two_pi`; there is no torus type. Jacobians are
`Fin n → Twist` column functions with a derived `6 × n` matrix view; the velocity
theorems hold for arbitrary, not only unit, joint twists. The
[Kinematics conventions](geometry-conventions.md#kinematics-conventions) record the
numbering, reference configuration and Jacobian ordering.

**Unverified:** the integrated build with these modules in `RoboLean.lean`; K13; a
nonempty dextrous-workspace instance (none is exhibited; the planar arm's is proved
empty); link-level agreement of the two K05 semantics beyond the tool; inverse
kinematics, singularities, closed chains and the planar annulus; numerical
behaviour, physical fidelity and user acceptance.

**Integrated gate (root, 2026-10-09 09:20:42 UTC):** the four I7 modules were added to `RoboLean.lean` and built with the whole library: [gate](../../docs/implogs/gates/E009/20261009T091745Z/) records `lake build` exit 0 in 9 s with no warning, and the whole-library audit ([output](../../docs/implogs/gates/E009/20261009T091745Z/axiom-audit.stdout)) lists 1602 constants across 58 modules (200 in the four new modules) with only `propext`, `Classical.choice` and `Quot.sound`, no `sorryAx`. Source hashes were unchanged during the gate. This supersedes the shadow-tree limit stated above for the I7 rows.

## Implementation evidence I8

E008, the `Wrench` carrier change and library hygiene ([entry](../../docs/implogs/E008-wrench-carrier-and-library-hygiene.md)), recorded by root at 2026-10-09 09:20:42 UTC. No row changes status. `Wrench` became an `@[ext]` two-field structure distinct from `Twist` (X47), `Twist.swapWrench` and `Wrench.toTwist` became explicit named identifications (X59), and `Wrench.finrank_eq_six` carries the dimension law (X63); the nine wrench-family modules and the hygiene edits (nine linter warnings cleared; MLS citations in `Geometry/RigidTransform`, `Geometry/RotationPlane`, `Examples/RigidTransform`) changed no library statement text ([statement diff](../../docs/implogs/gates/E008/20261009T084906Z/statement-diff.txt): 0 removed, 9 example literals rewritten). **Verified — integrated gate:** [gate](../../docs/implogs/gates/E008/20261009T091422Z/) records `lake build` exit 0 in 23 s with no warning on the 54 modules, and the whole-library audit lists 1402 constants with only the three standard axioms and no `sorryAx`. Type separation is Verified by the lead's [probe](../../docs/implogs/gates/E008/20261009T084906Z/TypeSeparation.lean) (14 `#check_failure` lines fail with type mismatches against the new carrier and succeed against the old). `Twist` remains `Vec3 × Vec3`; the lead's conversion recommendation is in the entry. Physical fidelity, numerics and user acceptance remain Unverified.

## Source evidence and cautions

The inspected local PDF has SHA-256
`c85b9e1b9465789812edb750254fc88faff2b1557763e7cf1aa1e85307fc4a02`.
Chapter 2 pp23-38 were extracted/read. Selected Chapter 3 passages were read at
pp83-89,95,115-122. Rendered pages 26,30,35,37,87,89,115,118 were visually
inspected, including page labels and matrix/sign conventions. The source-inspection
notes are prepared for E001; they are distinct from Lean proof evidence.

Three source cautions remain explicit:

1. R17: the nonunit Rodrigues display divides by `‖ω‖`; I3 now proves the
   explicit nonzero formula and a separate zero case.
2. R19-R20: rendered p30 eq2.18 divides by `sin θ`, while prose excludes only
   `θ=0`. A half-turn also has zero sine. This is a missing case of that displayed
   construction, not evidence against exponential surjectivity.
3. R25-R28: p33's quaternion group prose needs nonzero input; p34 uses unit
   quaternions for rotations. Reverse axis extraction also needs endpoint cases;
   it cannot yield a global single-valued smooth inverse.

These source cautions are mathematical inferences from inspected formulas.
I3 checks R17's explicit nonzero and zero cases. I5 checks rotation existence
without a sine denominator and generic axis recovery only under its explicit
nonzero-sine premise; it does not validate the printed extraction at a half turn.
I6 restricts quaternion group claims to the norm-one carrier; quaternion
rotation and half-angle bridges R27-R28 remain Unverified. No correction
silently replaces a printed statement. Proof evidence must identify Lean/mathlib v4.34.1 and exact checks;
a build alone does not establish physical-model fidelity.

The I3 reviewer additionally opened rendered printed pp27-31 and every page
pp39-69. The preserved source review and P2 proposal linked above record the
page ranges, commands, and normalization, zero-axis, signed-magnitude, and
reciprocity cautions. Appendix A brackets were not inspected in I3 and were outside I5. I6 now
records the separate bounded source inventory and four checked L rows.
