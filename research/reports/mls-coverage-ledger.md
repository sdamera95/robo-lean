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
specification), so 122 of the 126 selected obligations were Verified in full after I7.
[I8](#implementation-evidence-i8) records the distinct `Wrench` carrier and
[I9](#implementation-evidence-i9) the `Twist` structure; neither changes a row status.
[I10](#implementation-evidence-i10) adds K13, so 123 of the 126 Chapter 2, Appendix A and
Chapter 3 obligations are Verified in full and three remain Unverified: R27-R28 and X60 in
full. [I11](#implementation-evidence-i11) adds 24 selected Chapter 4 rows N01-N24, of which
N01-N16 are Verified and N17-N24 open (150 selected, 139 Verified at I11).
[I12](#implementation-evidence-i12) adds N17, N18, N19, N20 and N24 as Verified, with N21 partial
(parts (a)-(b) Verified, the bracket formula (4.30) open), giving 144 of 150.
[I13](#implementation-evidence-i13) adds 13 selected Chapter 3 rows K17-K29, of which K17-K26 are
Verified and K27-K29 open (163 selected, 154 Verified after I13).
[I14](#implementation-evidence-i14) adds 18 selected Chapter 4 §4-5 rows N25-N42, of which N25-N31
and N37-N39 are Verified in full, N33 and N40 are partial, and N32, N34-N36, N41, N42 open, so the
selected denominator was 181 with 164 Verified in full at I14.
[I16](#implementation-evidence-i16) adds K30 and moves K27–K30 to Verified: 182 selected, 168 Verified in full.
Open: R27, R28, X60 (partial), N21 (partial), N22, N23, N32, N33 (partial), N34, N35, N36, N40 (partial), N41, N42. The ten design
rows C01-C10 are counted separately and are not MLS obligations (C09-C10 from the Veil pilot E018,
[I15](#implementation-evidence-i15)).
These are selected-item counts,
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
| X | `RoboLean/Geometry/Twist.lean` | Two-field twist structure (`linear`, `angular`) with componentwise real vector space; independent twist matrix carrier and hat/vee linear equivalence |
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
| F | `RoboLean/Kinematics/ForcePullback.lean` | Joint torques as wrench–Jacobian pairings, power identity, transpose forms (K13) |
| C | `RoboLean/Examples/PlanarTwoLinkWorkspace.lean` | Planar two-link annulus and design certificates (C01–C07) |
| P | `RoboLean/Examples/PlanarTwoLink.lean` | Future two-revolute example |
| MN | `RoboLean/Kinematics/Manipulability.lean` | Manipulability measures μ₁–μ₃ and the alternative dextrous workspace W′_D (K29) |
| IK2 | `RoboLean/Examples/PlanarTwoLinkInverseKinematics.lean` | Planar two-link inverse kinematics, eq. (3.16) (K30) |
| EL | `RoboLean/Examples/ElbowManipulator.lean` | Elbow manipulator, Examples 3.2 and 3.5 (K28) |
| DS | `RoboLean/Design/PlanarArmSupervisor.lean` | Target supervisor mirrored from the Veil pilot, invariant and refinement (C09, C10) |

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
| X01 definition | p40 / 58, eq2.29 | X: `se(3)` as a linear part and an independently skew angular matrix | Real coordinates; no unit/nonzero premise | HT skew carrier; two-field twist structure with componentwise real module (E010) | Verified: [I4](#implementation-evidence-i4); `se3Submodule`, `Se3`, `mem_se3Submodule_iff` | Distinguish abstract twist coordinates from their homogeneous matrix representation |
| X02 definition | p41 / 59, eqs2.30-2.31 | X: twist hat and vee with hat(v,ω)=[[hat(ω),v],[0,0]] | Linear coordinates first; last row all zero | HT; block matrices; two-field structure carrier (E010) | Verified: [I4](#implementation-evidence-i4); `Twist.hat`, `Twist.vee`, [I9](#implementation-evidence-i9): `Twist.mk`, `Twist.ext`, `Twist.ext_iff`, `Twist.hat_angular`, `Twist.hat_linear`, `Twist.hat_lowerLeft`, `Twist.hat_lowerRight` | No bottom-right 1; that entry belongs to rigid transforms |
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
| K01 definition | pp83-84 / 101-102, joint-space discussion | K/P: configuration domain and admissible subset | Revolute periodicity; optional explicit limits | Angle quotient or real-lift periodicity | Verified: [I7](#implementation-evidence-i7); `SerialChain` (fields `twist`, `toolRef`, `admissible`), `SerialChain.fk_add_int_mul_two_pi`, `SerialChain.fk_update_add_two_pi`, `Twist.IsRevoluteJoint.exp_add_int_mul_two_pi`; since [I16](#implementation-evidence-i16) the field `admissible` is read by `SerialChain.admissibleCompleteWorkspace`, `admissibleReachableWorkspace`, `admissibleDextrousWorkspace` and `admissibleAlternativeDextrousWorkspace` (and, since I13, by `ClosedChain.admissible`) | `ℝ²` coordinates are not a torus equivalence by definition. I7: real lift `Fin n → ℝ` with a periodicity theorem for revolute joints; no quotient or torus type; `admissible` is an explicit set (default all of `Fin n → ℝ`); joint type is a hypothesis predicate, not a field. E009 review F4 resolved by giving the field a use (E020); the `Q`-parametrized definitions are unchanged |
| K02 definition | p85 / 103, eq3.1, Fig3.2; p94 / 112, eqs3.7-3.8, 3.10 | K/P: FK by adjacent-frame composition | Serial chain, base-to-tip order, tool offset | RT group/action, independently specified frames | Verified: [I7](#implementation-evidence-i7); `LinkFrameChain`, `LinkFrameChain.relative`, `LinkFrameChain.fk`; instance `Examples.planarTwoLinkFrames`, `Examples.planarTwoLinkFrames_fk` | First instance has two revolute joints; general chains later. I7: general `n`; the relative transform has the p85 form `exp(ζθ) g(0)` with `ζ` in the proximal link frame; the POE definition (eq3.3) is `SerialChain.fk` |
| K03 theorem | p87 / 105, revolute twist | K/P: reference joint twist `(-ω×q,ω)` | Unit axis, point on axis, base coordinates | P2 twist/exponential and axis semantics | Verified: [I7](#implementation-evidence-i7); `Twist.revolute`, `Twist.revolute_eq_fromScrew`, `Twist.revolute_axis_point`, `Twist.exp_revolute`, `Twist.exp_revolute_applyPoint`, `Twist.adjoint_revolute`, `Twist.IsRevoluteJoint` | Generalization needs independence of chosen point along axis. I7: definition is algebraic; the unit-axis premise is the explicit hypothesis of the exponential theorems; any point of `axisLine q ω` gives the same twist |
| K04 definition | p87 / 105, prismatic twist | K: reference prismatic twist `(v,0)` | Unit direction; displacement coordinate | Pure-translation exponential | Verified: [I7](#implementation-evidence-i7); `Twist.prismatic`, `Twist.IsPrismaticJoint`, `Twist.exp_prismatic`, `Twist.adjoint_prismatic` | Reusable target, not needed by two-revolute instance. I7: unit direction is the predicate `IsPrismaticJoint`; the exponential holds for every direction |
| K05 theorem | pp86-87 / 104-105, eqs3.2-3.3; p94 / 112, eqs3.7-3.10 | K/P: joint semantics equals ordered exponentials times reference pose | Constant reference twists; admissible angles | K02-K03, exponential conjugation/adjoint | Verified: [I7](#implementation-evidence-i7); sequential motion `SerialChain.moveJoint`, `runMoves`, `toolPose`, `moveJoint_linkPOE`, `toolPose_runMoves`, `toolPose_runMoves_perm`, `fk_single`; adjacent frames `LinkFrameChain.fk_eq_toSerialChain_fk`; instance `Examples.planarTwoLink_fk_eq_twoLinkPose` | Defining FK as POE and unfolding it is insufficient. I7: two independent semantics proved equal to POE (moves about current axes in any order; adjacent frames); arbitrary twists allowed; coordinate model only |
| K06 specification | pp87-89 / 105-107, Example 3.1 eq3.4, specialization | P: position as sum of rotated link displacements | Positive physical lengths, axes `+z`, zero links `+y` | R22, independent link/vector geometry | Verified: [I7](#implementation-evidence-i7); `Examples.planarTwoLinkPosition`, `Examples.planarTwoLinkPosition_eq` | New explicit geometric specification; positivity may be unused by algebra. I7: specification is the sum of the two `Rz`-rotated link vectors; `a, b` arbitrary reals, positivity unused |
| K07 theorem | p89 / 107, eq3.4, specialization | P: composed transform equals stated position and `Rz(q₁+q₂)` | `l₀=θ₃=θ₄=0`, `l₁=a`, `l₂=b` | K02, K06, angle addition | Verified: [I7](#implementation-evidence-i7); `Examples.planarTwoLink`, `Examples.planarTwoLink_fk`, `Examples.planarTwoLink_fk_rotation`, `Examples.planarTwoLink_fk_translation` | Specialized SCARA, not full four-joint example. I7: derived from the actual exponentials of the two revolute twists |
| K08 theorem | p84 / 102, revolute identification | P: FK is `2π`-periodic in each angle | Unrestricted ideal joints, real lift | K07, trigonometric periodicity | Verified: [I7](#implementation-evidence-i7); `Examples.planarTwoLink_fk_add_int_mul_two_pi` (from `SerialChain.fk_add_int_mul_two_pi`) | Explicit bridge to periodic configuration semantics. I7: integer multiples of `2π` in each angle; no torus equivalence type |
| K09 theorem | p115 / 133, differentiation; p118 / 136, final check | P/J: position derivative equals stated linear map on joint rates | Differentiable trajectory or Fréchet derivative | K07, derivative/trigonometric APIs | Verified: [I7](#implementation-evidence-i7); `Examples.hasDerivAt_planarTwoLink_translation` | Position Jacobian is not spatial twist Jacobian. I7: actual `HasDerivAt` along a joint trajectory with per-joint derivatives, not a Fréchet derivative in `θ` |
| K10 theorem | pp115-116 / 133-134, eqs3.51-3.54; p118 / 136, Example 3.8 | P/J: spatial Jacobian realizes `dot(g)g⁻¹` | `(v,ω)` order, same specialization | K05, adjoint, exponential/product derivative | Verified: [I7](#implementation-evidence-i7); `SerialChain.spatialJacobian`, `hasDerivAt_fk_toHomogeneous`, `spatialVelocity_fk`, `spatialJacobian_congr`, `spatialJacobianMatrix_mulVec`; instance `Examples.planarTwoLink_spatialJacobian_zero`, `Examples.planarTwoLink_spatialJacobian_one`, `Examples.planarTwoLink_spatialVelocity`, `Examples.planarTwoLink_spatialVelocity_eq_twoLinkPose` | Columns `(0,0,0,0,0,1)` and `(a cos q₁,a sin q₁,0,0,0,1)` need derivative proof. I7: general `n`, arbitrary (not only unit) twists; columns as `Fin n → Twist`, matrix view through `Twist.coordinates`; `spatialJacobian_eq_adjoint_linkPOE` is the definitional unfolding of the column (E009 review F3); the partial-derivative form of eqs3.52-3.53 is not stated, only trajectory derivatives (F7) |
| K11 theorem | p117 / 135, eq3.56 | J/P: `Jˢ=Ad_g Jᵇ` | Compatible spatial/body conventions | Velocity/adjoint relations, K10 | Verified: [I7](#implementation-evidence-i7); `SerialChain.bodyJacobian`, `spatialJacobian_eq_adjoint_bodyJacobian`, `bodyJacobian_eq_adjoint_inv_spatialJacobian`, `bodyVelocity_fk` | No arbitrary 6D Euclidean norm invariance follows. I7: column-wise identity for every real joint vector |
| K12 theorem | p117 / 135, point velocity; p118 / 136, final check | P/J: twist velocity at tool origin equals position derivative | Spatial point is `p(q)`, body origin is zero | K09-K10, twist action | Verified: [I7](#implementation-evidence-i7); `SerialChain.hasDerivAt_fk_translation`, `hasDerivAt_fk_translation_body`; planar check `Examples.planarTwoLink_point_velocity`, `Examples.hasDerivAt_planarTwoLink_translation_of_jacobian` | Must include `ω×p`; translational twist part alone is not `dot(p)`. I7: derivative is `ωˢ × p + vˢ` (spatial) and `R vᵇ` (body) |
| K13 theorem | p121 / 139, eqs3.59-3.60 | J/P: force pullback preserves instantaneous power | Matched wrench/Jacobian frames, arbitrary joint rates | Dual pairing, transpose identity, K10/K11 | Verified: [I10](#implementation-evidence-i10); `SerialChain.spatialWrenchTorques`, `bodyWrenchTorques`, `bodyJacobianMatrix`, `sum_spatialWrenchTorques_mul`, `sum_bodyWrenchTorques_mul`, `eq_spatialWrenchTorques_iff`, `eq_bodyWrenchTorques_iff`, `sum_spatialWrenchTorques_mul_eq_pair_spatialVelocity`, `sum_bodyWrenchTorques_mul_eq_pair_bodyVelocity`, `spatialJacobianMatrix_transpose_mulVec`, `bodyJacobianMatrix_transpose_mulVec`, `spatialWrenchTorques_transform`, `bodyWrenchTorques_transform_inv`; `Wrench.pair_eq_coordinates_dotProduct`, `Wrench.pair_sum_smul` | Algebraic identity separate from frictionless physical-work premise. I7: deferred (Wrench type change in progress). I10: torques are the pairing of the wrench with each Jacobian column; (3.59) body form with a body wrench at the tool origin, (3.60) spatial form; power identity for every joint-rate vector and along actual FK velocities; the "θ̇ free" step as an iff; spatial and body torques agree for wrenches related by `Wrench.transform (fk θ)` (eq2.67). Frictionless premise, time integral and the non-square-Jacobian caveat of p121 not formalized |
| K14 definition | p95 / 113, eq3.11 | W: complete workspace is FK image | Explicit admissible domain `Q` | FK, set image | Verified: [I7](#implementation-evidence-i7); `SerialChain.completeWorkspace`, `toolRef_mem_completeWorkspace`, `completeWorkspace_mono`; [I16](#implementation-evidence-i16) (`Q := c.admissible`): `SerialChain.admissibleCompleteWorkspace`, `admissibleCompleteWorkspace_subset` | Pose reachability, not path or dynamic feasibility. I7: `Q` is an explicit argument |
| K15 definition | p95 / 113, eq3.12 | W/P: reachable workspace is position image | Same domain `Q` | Position projection, set image | Verified: [I7](#implementation-evidence-i7); `SerialChain.reachableWorkspace`, `reachableWorkspace_eq_image`, `reachableWorkspace_mono`, `toolRef_translation_mem_reachableWorkspace`, `reachableWorkspace_of_zero_joints`; [I16](#implementation-evidence-i16) (`Q := c.admissible`): `SerialChain.admissibleReachableWorkspace`, `admissibleReachableWorkspace_subset`, `admissibleReachableWorkspace_of_admissible_eq_univ`, instance `Examples.planarTwoLink_admissibleReachableWorkspace_eq` | Does not quantify over all orientations. I7: `Q` is an explicit argument |
| K16 definition | p95 / 113, eq3.13 | W: dextrous workspace uses `∀R,∃q` realizing `(p,R)` | Orientations range over `SO(3)` | Pose FK, explicit quantifier order | Verified: [I7](#implementation-evidence-i7); `SerialChain.dextrousWorkspace`, `mem_dextrousWorkspace_iff`, `dextrousWorkspace_subset_reachableWorkspace`, `dextrousWorkspace_mono`, `dextrousWorkspace_of_zero_joints`; planar `Examples.planarTwoLink_dextrousWorkspace_eq_empty`, `Examples.planarTwoLink_reachableWorkspace_nonempty`; [I16](#implementation-evidence-i16) (`Q := c.admissible`): `SerialChain.admissibleDextrousWorkspace`, `admissibleDextrousWorkspace_subset` | Planar pilot cannot realize arbitrary 3D orientations; name any planar variant separately. I7: `∀R,∃θ∈Q` as printed; the planar pilot's 3D dextrous workspace is proved empty; no planar-orientation variant is defined; no nonempty-dextrous instance is exhibited |
| K17 theorem | pp99-100 / 117-118, eqs3.17-3.19 | IK: Subproblem 1, rotation about a single axis: existence condition, atan2 solution, branch structure | `ξ = Twist.revolute ω r` with `‖ω‖ = 1` (zero-pitch unit twist, `r` on the axis); `u = p − r`, `v = q − r`; `u′ = perp ω u`; angles modulo `2π` | K03, Rodrigues on vectors, `Rotation.atan2` | Verified: [I13](#implementation-evidence-i13); `PadenKahan.applyPoint_exp_revolute_eq_iff`, `subproblemOne_iff_sum_eq_zero`, `subproblemOne_necessary`, `subproblemOne_planeAngle`, `subproblemOne_exists_iff`, `subproblemOne_iff`, `subproblemOne_of_perp_eq_zero`; supporting `PadenKahan.perp`, `inner_perp`, `norm_perp_sq`, `inner_perp_perp`, `cross_perp`, `exp_act_eq`, `planeAngle`, `norm_sub_exp_act_sq`, `Rotation.sqrt_mul_cos_atan2`, `Rotation.sqrt_mul_sin_atan2` (in `Geometry/EulerAngles.lean` since [I16](#implementation-evidence-i16); the `PadenKahan.` names no longer exist) | Existence iff (3.19); the atan2 angle solves whenever (3.19) holds, also for `u′ = 0`; solutions exactly `θ₀ + 2πk` when `u′ ≠ 0`; for `u′ = 0` (under (3.19)) `p = q` lies on the axis and every angle solves; `atan2 0 0 = 0` is a convention |
| K18 theorem | pp100-102 / 118-120, eqs3.20-3.25 | IK: Subproblem 2, two subsequent rotations about intersecting axes: decomposition (3.24), existence, zero/one/two branches | unit `ω₁, ω₂`; intersecting axes modelled by one axis point `r` for both twists; main case `ω₁ × ω₂ ≠ 0`; `Γ` = the printed right side for `γ²` | K17 | Verified: [I13](#implementation-evidence-i13); `PadenKahan.subproblemTwo_iff_act`, `subproblemTwo_coincident`, `subproblemTwoAlpha`, `subproblemTwoBeta`, `subproblemTwoGammaSq`, `subproblemTwoPoint`, `inner_subproblemTwoPoint_left`, `inner_subproblemTwoPoint_right`, `norm_subproblemTwoPoint_sq`, `eq_subproblemTwoPoint`, `inner_exp_act_axis`, `exists_exp_act_eq_iff`, `subproblemTwo_iff`, `subproblemTwo_exists_of_sq_eq`, `subproblemTwo_exists_iff`, `subproblemTwoPoint_injective`, `subproblemTwo_intermediate`, `subproblemTwo_two_solutions`, `subproblemTwo_intermediate_of_eq_zero`, `subproblemTwo_no_solution` | Existence iff `‖p − r‖ = ‖q − r‖` and `Γ ≥ 0`: the equal-norm condition is among the book's consequences on p101 but its procedure states only the `γ` count; branches counted as intermediate points `c` of (3.21) (`Γ < 0` none, `Γ = 0` one, `Γ > 0` two distinct); the number of angle pairs, which also depends on `p` or `q` lying on an axis, is not formalized; coincident axes: `(θ₁, θ₂)` solves iff `θ₁ + θ₂` solves Subproblem 1 |
| K19 theorem | pp102-103 / 120-121, eqs3.26-3.29 | IK: Subproblem 3, rotation to a given distance: projected distance, law of cosines, `θ₀ ± cos⁻¹ κ`, zero/one/two branches | unit `ω`; `δ ≥ 0`; `u′ ≠ 0`, `v′ ≠ 0`; `κ = subproblemThreeCos`; angles modulo `2π` | K17 identity | Verified: [I13](#implementation-evidence-i13); `PadenKahan.subproblemThree_norm_sq`, `subproblemThreeCos`, `subproblemThree_iff_cos`, `subproblemThree_iff`, `subproblemThree_no_solution`, `subproblemThree_branches_eq_of_abs_eq_one`, `subproblemThree_branches_ne_of_abs_lt_one`, `subproblemThree_norm_eq_of_perp_eq_zero` | Adds `u′ ≠ 0`, `v′ ≠ 0`, which the book does not state (it divides by `‖u′‖‖v′‖` in (3.29)); `δ ≥ 0` is weaker than the book's `δ > 0`; `δ′²` may be negative and enters only through `κ`; degenerate case: the distance does not depend on `θ` |
| K20 definition | p123 / 141 | S: singular configuration, the Jacobian drops rank | `rank (spatialJacobianMatrix c θ) < min 6 n`; real lift; admissibility not part of the definition | K10 | Verified: [I13](#implementation-evidence-i13); `SerialChain.IsSingular`, `col_spatialJacobianMatrix`, `rank_spatialJacobianMatrix`, `rank_spatialJacobianMatrix_le`, `linearIndependent_spatialJacobian_iff`, `isSingular_iff_not_linearIndependent`, `isSingular_iff_not_linearIndependent_bodyJacobian`; `Twist.coordinatesEquiv`, `Twist.coordinatesEquiv_apply` (`Twist.coordinatesEquiv`, `Twist.coordinatesEquiv_apply` in `Geometry/TwistAdjoint.lean` since [I16](#implementation-evidence-i16), names unchanged) | For `n ≤ 6` iff the twist columns are linearly dependent (the printed readings); `n > 6` (rank below six) is the library's extension; body-Jacobian form for `n ≤ 6` (pp125, 128) |
| K21 theorem | pp124-125 / 142-143, Example 3.11 | S: two collinear revolute joints give a singular configuration | `n ≤ 6`; distinct columns `i ≠ j` that are revolute twists of the current axes; `ω₂ = ±ω₁`; `ω₁ × (q₁ − q₂) = 0` | K20, K03 (`Twist.adjoint_revolute`) | Verified: [I13](#implementation-evidence-i13); `SerialChain.isSingular_of_collinear_revolute`, `SerialChain.not_linearIndependent_of_eq_smul`, `Twist.revolute_eq_of_cross_sub_eq_zero`, `Twist.revolute_eq_smul_of_collinear` (the `Twist.revolute_*` lemmas in `Kinematics/SerialChain.lean` since [I16](#implementation-evidence-i16), names unchanged) | Book: six-joint manipulator; Lean: every `n ≤ 6`; unit magnitude not needed; the `i = 2` collinearity condition follows from the `i = 1` one and parallelism |
| K22 theorem | p126 / 144, Example 3.13 | S: four revolute axes through one point give a singular configuration | `n ≤ 6`; injective `f : Fin 4 → Fin n`; `ωₖ × (qₖ − q) = 0` | K20 | Verified: [I13](#implementation-evidence-i13); `SerialChain.isSingular_of_four_concurrent_revolute`, `Twist.revoluteLinear`, `Twist.revoluteLinear_apply` (`Twist.revoluteLinear`, `_apply` in `Kinematics/SerialChain.lean` since [I16](#implementation-evidence-i16), names unchanged) | Proof by dimension count (the columns lie in the three-dimensional space of revolute twists through `q`), not the book's reciprocal-system argument; every `n ≤ 6` |
| K23 theorem | p123 / 141, with p118 / 136; planar specialization | S/P: the planar two-link arm in the p123 sense | twist order `(v, ω)`; arbitrary real `a, b` | K10 instance, K20 | Verified: [I13](#implementation-evidence-i13); `Examples.planarTwoLink_spatialJacobian_eq`, `Examples.planarTwoLink_isSingular_iff`, `Examples.planarTwoLink_not_isSingular` | Singular iff `a = 0`: for `a ≠ 0` the 6 × 2 spatial Jacobian has rank 2 at every configuration, so the folded configurations are not singular in the p123 sense (they are for the position map, C08); a specialization, not a printed example |
| K24 definition | pp132-133 / 150-151, eq3.65 | CC: joint space `Q′` of a closed chain (structure equation) | two serial chains, one base and one tool frame; `Q′` includes each chain's admissible set | K01, K05 | Verified: [I13](#implementation-evidence-i13); `ClosedChain` (with `ClosedChain.mk`, `chain₁`, `chain₂`), `ClosedChain.admissible`, `mem_admissible_iff`, `fk`, `fk_eq_chain₂`, `zero_mem_admissible_iff` | Two chains only (the book allows two or more; (3.69) uses `k`); the reference tool poses may differ, and their equality is exactly `(0, 0) ∈ Q′` (the book writes one `g_st(0)`) |
| K25 theorem | p133 / 151, eq3.67 | CC: differential of the structure equation, `J₁ˢθ̇₁ = J₂ˢθ̇₂ = Vˢ` | joint trajectories with `HasDerivAt` rates at `t`; loop closed for all `s` near `t` | K10 | Verified: [I13](#implementation-evidence-i13); `ClosedChain.spatialVelocity_chain₂_eq`, `ClosedChain.sum_spatialJacobian_eq` | Along actual loop-closing trajectories; no claim that `Q′` is a manifold or that every rate pair satisfying the linear constraint is tangent to `Q′` (would need a rank hypothesis and an implicit-function argument) |
| K26 definition | p134 / 152, eqs3.69-3.70 | CC: admissible end-effector velocities and the rank `ρ` of the structure equations | two chains | K25 | Verified: [I13](#implementation-evidence-i13); `ClosedChain.admissibleVelocities`, `mem_admissibleVelocities_iff`, `structureRank`, `structureRank_le`, `sum_spatialJacobian_mem_admissibleVelocities` | The predicate \"kinematically singular when `ρ` drops\" is not defined (the book compares with nearby configurations without fixing the comparison); actuator singularities not formalized |
| K27 theorem | pp125-126 / 143-144, Example 3.12 | S: three parallel coplanar revolute axes give a singular configuration | `n ≤ 6`; injective `f : Fin 3 → Fin n`; columns `f k` of `Jˢ(θ)` are revolute twists `(-ωₖ × qₖ, ωₖ)` of the current axes (p116); `ωᵢ = ωⱼ ∨ ωᵢ = -ωⱼ` for all `i, j` (condition 1 as printed); unit normal `ν` (the book's `n`) with `νᵀωᵢ = 0` and `νᵀ(qᵢ − qⱼ) = 0` for all `i, j` (condition 2) | K20, K03 | Verified: [I16](#implementation-evidence-i16); `SerialChain.isSingular_of_three_parallel_coplanar_revolute`; the printed instance "the elbow manipulator exhibits this singularity in its reference configuration" (p126) is `Examples.elbowManipulator_isSingular_zero` | Book: six-degree-of-freedom manipulator; Lean: every `n ≤ 6`. Proof by dimension count (with `ω = ω₀`, each column is `±((-ω × q₀, ω) − c (ν, 0))`, so the three columns lie in a two-dimensional span), not the book's adjoint change of frame; unit `ν` is used (any nonzero normal would do) |
| K28 theorem | pp89-91 / 107-109, Example 3.2; pp104-106 / 122-124, Example 3.5, eqs3.30-3.37 | IK: the elbow manipulator, its forward kinematics as printed, and its inverse kinematics assembled from Subproblems 1–3 | `Examples.elbowManipulator l₀ l₁ l₂ : SerialChain 6` with the twists of Fig. 3.4 (axes `+z, −x, −x, +z, −x, +y` through `(0,0,l₀)`, `(0,0,l₀)`, `(0,l₁,l₀)` and the wrist centre `p_w = (0, l₁+l₂, l₀)`), `g_st(0) = (I, p_w)`; all real lengths; `p_b = (0,0,l₀)`; `g₁ = g_d g_st(0)⁻¹`; `e^{−ξ̂θ}` is `Twist.exp ξ (−θ)`; angles modulo `2π` | K05, K17–K19, K27 | Verified: [I16](#implementation-evidence-i16); `Examples.elbowManipulator`, `elbowShoulder`, `elbowWrist`, `elbowManipulator_twist_zero` … `_twist_five`, `elbowManipulator_isRevoluteJoint`, `elbowRotationMatrix`, `elbowManipulator_fk_rotation`, `elbowManipulator_fk_translation`, `elbowManipulator_poe`, `SerialChain.fk_eq_iff_poe_eq`, `elbowManipulator_wrist_eq`, `elbowManipulator_subproblemThree`, `elbowManipulator_elbow_angle`, `elbowManipulator_subproblemTwo_shoulder`, `elbowManipulator_shoulder_axes_cross_ne_zero`, `elbowManipulator_subproblemTwo_wrist`, `elbowManipulator_subproblemOne`, `elbowManipulator_fk_eq_of_subproblems`, `elbowManipulator_fk_eq_iff`; supporting `Twist.exp_revolute_applyPoint_of_mem_axisLine` | Forward kinematics: the twists, `R(θ)` (all nine printed entries) and `p(θ)` as printed, for all real lengths. Inverse kinematics: necessity of each step in the exact form of the K17–K19 subproblem (Step 1: Subproblem 3 with `p = p_w`, `q = p_b`, `δ = ‖g₁p_w − p_b‖`, and `θ₃ = θ₀ ± cos⁻¹κ` mod `2π` under `l₁, l₂ ≠ 0`, which the book does not state; Step 2: Subproblem 2 through `p_b`; Step 3: Subproblem 2 through `p_w` for every point of the sixth axis; Step 4: Subproblem 1 for every point), and the converse: for `p ≠ p_w` on the sixth axis and `p′` off it, `g_st(θ) = g_d` iff (3.34), (3.36) at `p` and (3.37) at `p′` (a rigid motion fixing three non-collinear points is the identity). Not formalized: "a maximum of eight possible solutions" (p106) and the finiteness of each subproblem's solution set. Root may record the row as partial for the count |
| K29 definition | pp127-129 / 145-147, §4.4, Examples 3.14-3.16, eq3.61 | S: manipulability measures `μ₁ = σ_min(J)`, `μ₂ = σ_min/σ_max`, `μ₃ = det J`, and the alternative dextrous workspace `W′_D = {g_st(θ) : θ ∈ Q, μᵢ(θ) ≠ 0}` | `J` = `bodyJacobianMatrix` (the book's preference, p128); singular values = Mathlib `LinearMap.singularValues` of `Matrix.toEuclideanLin J` (square roots of the eigenvalues of `JᵀJ`, decreasing, index `0` = `σ_max`, index `n − 1` = `σ_min`), standard inner products on joint rates and on the six coordinates `(v, ω)`; `μ₃` for `n = 6`, rows `(v, ω)`, columns joints in order; `W′_D` takes `Q` and `μ` explicitly | K11, K13 (`bodyJacobianMatrix`), K14, K20; Mathlib `SingularValues`, `NormDet` | Verified: [I16](#implementation-evidence-i16); `SerialChain.jacobianSingularValues`, `hasEigenvalue_transpose_mul_bodyJacobianMatrix`, `maxSingularValue`, `minSingularValue`, `inverseConditionNumber`, `jacobianDet`, `jacobianDet_eq_det_square`, `minSingularValue_eq_zero_iff_isSingular`, `inverseConditionNumber_eq_zero_iff_isSingular`, `jacobianDet_eq_zero_iff_isSingular`, `abs_jacobianDet_eq_prod_singularValues`, `jacobianDet_eq_det_spatial`, `minSingularValue_nonneg`, `minSingularValue_le_maxSingularValue`, `inverseConditionNumber_nonneg`, `inverseConditionNumber_le_one`, `minSingularValue_eq_zero_iff_rank_lt`, `alternativeDextrousWorkspace`, `admissibleAlternativeDextrousWorkspace`, `alternativeDextrousWorkspace_subset_completeWorkspace`, `alternativeDextrousWorkspace_eq_of_iff`, `alternativeDextrousWorkspace_minSingularValue`, `alternativeDextrousWorkspace_inverseConditionNumber`, `alternativeDextrousWorkspace_jacobianDet`, `mem_alternativeDextrousWorkspace_iff_forall`, `not_isSingular_iff_forall_exists_rate`; supporting `spatialJacobianMatrix_eq_adjointMatrix_mul`, `rank_bodyJacobianMatrix`, `Twist.det_adjointMatrix` | Zero-set theorems ("at a singular configuration … is zero", p128, with converses) need `0 < n ≤ 6` (`μ₃`: `n = 6`). `|μ₃| = ∏σᵢ`: the book says `det J` "is the product of the singular values"; the determinant can be negative. The values of `μ₁`, `μ₂` depend on the Jacobian's frame and on the coordinate inner product; their zero sets do not; `μ₃` is the same for spatial and body Jacobians. The three measures give the same `W′_D`, the image of the nonsingular configurations in `Q`; "can move infinitesimally in any direction" is proved for `n = 6` as: every twist is `Jˢ(θ) θ̇`. Not formalized: `σ_max(A) = ‖A‖₂`, the velocity and ellipsoid-volume interpretations; for `n > 6`, `σ_min` (index `n − 1`) is always `0` |
| K30 theorem | pp97-98 / 115-116, §3.1, eq3.16 | IK: planar two-link closed-form inverse kinematics: `θ₂ = π ± α`, `θ₁ = atan2(y, x) ± β` with agreeing signs, all solutions, no solution for `r > l₁ + l₂` | the book's point `(x, y)` (Fig. 3.7a, zero configuration along `+x`) is the library point `vec (−y) x 0` of `planarTwoLinkPosition a b` (zero configuration along `+y`); `l₁ = a`, `l₂ = b`, `θ₁ = q 0`, `θ₂ = q 1`; `0 < a`, `0 < b`; `r = √(x² + y²)`, `0 < r`, `|a − b| ≤ r ≤ a + b`; `cos⁻¹` = `Real.arccos`, `atan2` = `Rotation.atan2`; angles modulo `2π` | K06–K07, C01, K19 (branch lemmas) | Verified: [I16](#implementation-evidence-i16); `Examples.planarTwoLinkAlpha`, `planarTwoLinkBeta`, `planarTwoLinkPosition_eq_vec_iff`, `norm_vec_neg`, `planarTwoLink_elbow_iff`, `planarTwoLink_elbow_branches_ne_iff`, `planarTwoLink_elbow_no_solution`, `planarTwoLink_inverseKinematics_iff`, `planarTwoLink_inverseKinematics_plus`, `planarTwoLink_inverseKinematics_minus`, `planarTwoLink_inverseKinematics_origin`, `planarTwoLink_inverseKinematics_no_solution`, `arccos_elbow_eq_pi_sub_alpha` | Adds `0 < l₁, l₂` and `r ≠ 0`, which the book does not state (it divides by `l₁ l₂` and by `r`); the case `r = 0` (only for `l₁ = l₂`) is separate: `θ₂ ≡ π`, `θ₁` arbitrary. No solution also for `r < |l₁ − l₂|` (not printed; the inner circle of C01). The two `θ₂` values are distinct modulo `2π` exactly when `|l₁ − l₂| < r < l₁ + l₂`; source observation: the book's "if `α ≠ 0`, there are two distinct values of `θ₂`" does not exclude `α = π` (`r = l₁ + l₂`), where `0` and `2π` are distinct reals naming one angle (p84). C02's elbow angle is the `π − α` branch |

The annulus theorem for positive lengths and unrestricted joints is a derived design
target, not a quoted theorem from the inspected pages; rows C01–C07 in
[Design certificates beyond MLS](#design-certificates-beyond-mls) now cover both
inclusions, zero radius, and equal lengths. Joint limits,
collision avoidance, continuous IK selection, and motion feasibility are separate.

### Design certificates beyond MLS

These rows are design statements from [the assessment](mls-lean-assessment.md)
("Robot design and workspace coverage"), not results printed in MLS. They use the
reachable workspace of [p95 eq3.12](../../references/MLS.pdf#page=113) for the planar
two-link specialization `Examples.planarTwoLink a b` (K06–K07). MLS Example 3.4
([pp96-97](../../references/MLS.pdf#page=114)) describes the analogous two-link annulus
only informally, as a step of a three-link construction in another frame, and
[p98](../../references/MLS.pdf#page=116), eq3.16, prints the closed-form inverse kinematics
`θ₂ = π ± α` with the remark that no solution exists for `r > l₁ + l₂` (found by the E011
review); the workspace equality and the certificates below are not printed. The C rows are
counted separately from the 181 MLS selected obligations. Rows C09 and C10 come from the Veil pilot ([E018](../../docs/implogs/E018-veil-pilot-planar-arm-supervisor.md)): a supervisor model whose first-evaluation recipe is in [veil-robotics-verification.md](veil-robotics-verification.md), not from MLS or the assessment.

| ID / kind | Source | Intended statement/module | Assumptions/conventions | Dependencies or missing bridge | Formal status | Statement divergence |
| --- | --- | --- | --- | --- | --- | --- |
| C01 theorem | assessment "Robot design and workspace coverage"; p95 / 113, eq3.12 | W: reachable workspace lies in the annulus | `0 ≤ a`, `0 ≤ b`, `Q = Set.univ`; plane is `x 2 = 0` | K07, law of cosines | Verified: [I10](#implementation-evidence-i10); `Examples.planarTwoLink_reachableWorkspace_subset`, `Examples.planarTwoLinkPosition_mem_annulus`, `Examples.planarTwoLinkPosition_norm_sq`, `Examples.planarTwoLinkPosition_two` | Assessment states positive lengths; the easy inclusion holds for nonnegative ones. The planar point is a `Vec3` with third coordinate zero |
| C02 theorem | same; p98 / 116, eq3.16 | W/IK: every annulus point is reached by some joint vector | `0 < a`, `0 < b`, `Q = Set.univ` | `Real.arccos`, `Complex.arg` | Verified: [I10](#implementation-evidence-i10); `Examples.exists_planarTwoLinkPosition_eq`, `Examples.planarTwoLink_annulus_subset_reachableWorkspace` | Existence by construction (`θ₂ = arccos((‖x‖²−a²−b²)/(2ab))`, `θ₁` a complex argument); no uniqueness, branch choice or continuity; MLS p98, eq3.16, prints `θ₂ = π ± α` with `α = cos⁻¹((l₁² + l₂² − r²)/(2l₁l₂))` and the no-solution remark for `r > l₁ + l₂`, the chosen angle is the `π − α` branch (E011 review F1; `Examples.arccos_elbow_eq_pi_sub_alpha`, [I16](#implementation-evidence-i16)); for `‖x‖ > 0` every solution, the constructed one included, is one of the two printed branches (K30) |
| C03 theorem | same | W: reachable workspace equals the annulus | `0 < a`, `0 < b`, `Q = Set.univ` | C01, C02 | Verified: [I10](#implementation-evidence-i10); `Examples.planarTwoLink_reachableWorkspace_eq` | Position only; no orientation, joint limits or collisions |
| C04 theorem | assessment, `∀x∈W, ∃q∈Q_d, FK_d(q)=x` | Design certificate for a task region `W` | `0 < a`, `0 < b`; `W` in the plane with `\|a−b\| ≤ ‖x‖ ≤ a+b` | C02, C03 | Verified: [I10](#implementation-evidence-i10); `Examples.planarTwoLink_workspace_certificate`, `Examples.planarTwoLink_subset_reachableWorkspace_iff` | The iff adds necessity of the condition. Position reachability of the ideal model only |
| C05 theorem | assessment, "check that a prescribed radial band lies within those bounds" | Radial-band certificate | `\|a−b\| ≤ r₁`, `r₂ ≤ a+b`, `0 < a`, `0 < b` | C02 | Verified: [I10](#implementation-evidence-i10); `Examples.planarTwoLink_radialBand_certificate` | Band `r₁ ≤ ‖x‖ ≤ r₂` in the plane `x 2 = 0` |
| C06 theorem | assessment, "Equal lengths allow the base-centered disk"; ledger note after K16 | Zero radius and equal lengths | `0 < a`, `0 < b` | C03 | Verified: [I10](#implementation-evidence-i10); `Examples.zero_mem_planarTwoLink_reachableWorkspace_iff`, `Examples.planarTwoLink_reachableWorkspace_eq_disk` | Origin reachable iff `a = b`; for `a = b` the workspace is the disk `‖x‖ ≤ 2a` |
| C07 theorem | assessment, "the origin is a singular configuration" | Equal-length origin configurations | `a ≠ 0`, equal lengths | law of cosines | Verified: [I10](#implementation-evidence-i10); `Examples.planarTwoLinkPosition_eq_zero_iff` | Position condition `cos θ₂ = −1` only; no Jacobian rank or singularity theorem; see C08 (position Jacobian) and K23 (p123 sense) |
| C08 theorem | assessment, \"the origin is a singular configuration\"; p131 / 149, eq3.64 (position Jacobian, printed for three links) | Position-Jacobian singularities of the planar two-link arm | `a ≠ 0`, `b ≠ 0` (`0 < a`, `0 < b` for the boundary form); `q 0 = θ₁`, `q 1 = θ₂`; zero configuration along `+y` | K09, C01, C07 | Verified: [I13](#implementation-evidence-i13); `Examples.planarTwoLinkPositionJacobian`, `hasDerivAt_planarTwoLink_translation_eq_positionJacobian`, `det_planarTwoLinkPositionJacobian`, `det_planarTwoLinkPositionJacobian_eq_zero_iff`, `exists_planarTwoLink_null_rate_iff`, `det_planarTwoLinkPositionJacobian_eq_zero_iff_exists_int`, `det_planarTwoLinkPositionJacobian_eq_zero_iff_norm`, `det_planarTwoLinkPositionJacobian_eq_zero_of_position_eq_zero` | `det ∂p/∂θ = ab sin θ₂`; singular iff `θ₂ ∈ πℤ` iff the tool lies on a boundary circle of the annulus; C07's origin configurations are among them. A statement about the position map, not the p123 definition (K23) |
| C09 theorem | Veil pilot design (E018); [veil-robotics-verification.md](veil-robotics-verification.md), "Practical constraints and a first evaluation" | Supervisor invariant: in every reachable state of the target supervisor, every commanded target satisfies the guard; `Design/PlanarArmSupervisor` | Any target type and any guard `reachable : Target → Prop`; reachable states are `Relation.ReflTransGen (Step reachable) init`; Veil Boolean relations are Lean sets | Mathlib `Relation.ReflTransGen`; mirrors the Veil model `robo-lean-veil/Examples/RoboLean/PlanarArmSupervisor.lean` by a recorded convention, no kernel link (D003) | Verified: [I15](#implementation-evidence-i15); `Design.PlanarArmSupervisor.State`, `init`, `Step`, `ReachableState`, `CommandedReachable`, `commandedReachable_init`, `Step.commandedReachable`, `ReachableState.commandedReachable` | Veil checks one verification condition per (action, clause) and emits no theorem that composes them along runs; the Lean theorem is that composition for the mirrored system. The action ending a command is `finish`, since Veil reserves `complete` |
| C10 theorem | C04 with C09; [p95](../../references/MLS.pdf#page=113) / 113, eq3.12; [p98](../../references/MLS.pdf#page=116) / 116, eq3.16 | Refinement: with guard `planarGuard a b`, every target commanded in a reachable state is a tool position `planarTwoLinkPosition a b q`, and the commanded set lies in `W_R` | `0 < a`, `0 < b`; `planarGuard a b x` is C04's condition `x 2 = 0 ∧ \|a − b\| ≤ ‖x‖ ≤ a + b` exactly; targets are points `Vec3` or carry positions `pos : Target → Vec3`; `Q = Set.univ` | C09, C04 (`planarTwoLink_workspace_certificate`, `planarTwoLink_subset_reachableWorkspace_iff`), C02 | Verified: [I15](#implementation-evidence-i15); `Design.planarGuard`, `Design.PlanarArmSupervisor.ReachableState.exists_planarTwoLinkPosition_eq_pos`, `ReachableState.exists_planarTwoLinkPosition_eq`, `ReachableState.commanded_subset_reachableWorkspace` | Position reachability of the ideal model only; the Veil model's `reachable` read as `planarGuard a b` is a convention; nothing about the sampled implementation, timing, motion between targets, orientation, joint limits or collisions |

## Chapter 4 dynamics obligations

Selected by [E012](../../docs/implogs/E012-rigid-body-inertia-and-mass-matrix.md) from Chapter 4,
printed pp. 155–178 (PDF 173–196): 24 obligations, 16 landed in I11 and 8 open. This is a
selected inventory, not a measure of Chapter 4 or of the book. Lean link `k : Fin n` is the
book's link `k + 1` and Lean joint `j` the book's joint `j + 1`. Modules:
[RigidBodyInertia](../../RoboLean/Dynamics/RigidBodyInertia.lean),
[MassMatrix](../../RoboLean/Dynamics/MassMatrix.lean),
[Christoffel](../../RoboLean/Dynamics/Christoffel.lean),
[PlanarTwoLinkDynamics](../../RoboLean/Examples/PlanarTwoLinkDynamics.lean).

| ID / kind | Source printed / PDF | Intended statement/module | Assumptions/conventions | Dependencies or missing bridge | Formal status | Statement divergence |
| --- | --- | --- | --- | --- | --- | --- |
| N01 definition | p162 / 180, eq4.9 | Generalized inertia `𝓜 = [[mI,0],[0,𝓘]]` and rigid-body kinetic energy `½ Vᵇ·𝓜Vᵇ`; `Dynamics/RigidBodyInertia` | Body frame at the mass center for the block form; rows/columns `Fin 3 ⊕ Fin 3` in twist order `(v, ω)` | `Twist.coordinates` | Verified: [I11](#implementation-evidence-i11); `RigidBody.generalizedInertia`, `RigidBody.kineticEnergy` | `𝓘` is any real 3×3 matrix, not the mass integral `-∫ρ r̂² dV`; no symmetry or sign built in |
| N02 theorem | p162 / 180, eq4.9 first line | `½Vᵀ𝓜V = ½m‖v‖² + ½ωᵀ𝓘ω`, and for an actual pose trajectory `½m‖ṗ‖² + ½(ωᵇ)ᵀ𝓘ωᵇ` | Actual `HasDerivAt` of the homogeneous pose; `ṗ` the actual translation derivative | `RigidTransform.bodyVelocity`, `hasDerivAt_translation`, `Rotation.norm_act` | Verified: [I11](#implementation-evidence-i11); `RigidBody.kineticEnergy_generalizedInertia`, `RigidBody.kineticEnergy_generalizedInertia_bodyVelocity`, `RigidBody.dotProduct_generalizedInertia_mulVec`, `RigidBody.coordinates_dotProduct_generalizedInertia_mulVec` | The book's volume-integral derivation (pp161–162, centre-of-mass cancellation) is not formalized; the identity starts from the block matrix |
| N03 theorem | p162 / 180, "symmetric and positive definite"; p171 / 189 proof idea | `𝓜` symmetric for symmetric `𝓘`; PSD for `0 ≤ m`, PSD `𝓘`; PD for `0 < m`, PD `𝓘`; kinetic energy `≥ 0`, `> 0` off rest, `= 0 ↔ V = 0` | Explicit hypotheses on `m`, `𝓘` | Mathlib `Matrix.PosSemidef`/`PosDef` (Finsupp definition, `posSemidef_iff_dotProduct_mulVec`) | Verified: [I11](#implementation-evidence-i11); `RigidBody.generalizedInertia_isSymm`, `_posSemidef`, `_posDef`, `RigidBody.kineticEnergy_nonneg`, `_pos`, `_eq_zero_iff` | MLS prints PD with no hypothesis; positivity of `m` and `𝓘` is assumed, not derived from a density; physical realizability (triangle inequalities on principal moments) not addressed |
| N04 definition | p176 / 194, eq4.28 | Transformed inertia `Ad_gᵀ 𝓜 Ad_g` for a body-fixed frame change `g = g_BC` | `Twist.adjointMatrix` in order `(v, ω)`; (4.28) is `g = g_{sl_i}(0)⁻¹` | X-row adjoint matrix (`Twist.adjointMatrix`, `adjointMatrix_mulVec`) | Verified: [I11](#implementation-evidence-i11); `RigidBody.transformInertia` | General `g`; the book uses only `g_{sl_i}(0)⁻¹` |
| N05 theorem | p176–177 / 194–195, eq4.28, Ex4.4; p59 / 77, Prop2.15 | Kinetic energy invariant under the frame change (algebraic, and for actual trajectories `g(t)h`); composition, identity; symmetry, PSD, PD preserved; pure-translation block form `[[mI, m p̂],[-m p̂, 𝓘 - m p̂²]]` | Constant `h = g_BC`; actual derivative of `g(t)` | `RigidTransform.bodyVelocity_mul`, `adjointMatrix_mul`, `adjointMatrix_inv` | Verified: [I11](#implementation-evidence-i11); `RigidBody.kineticEnergy_transformInertia`, `RigidBody.kineticEnergy_bodyVelocity_mul_const`, `RigidBody.coordinates_dotProduct_transformInertia_mulVec`, `RigidBody.transformInertia_one`, `_mul`, `_isSymm`, `_posSemidef`, `_posDef`, `RigidBody.adjointMatrix_mulVec_injective`, `RigidBody.transformInertia_translation` | Observation (consistency check, not an errata judgment): the p177 display's right-hand side `[[mI, m p̂],[-m p̂, 𝓘]]` is not the product of its displayed factors `Ad_{(I,p)}ᵀ 𝓜 Ad_{(I,p)}`, which has lower-right block `𝓘 - m p̂²`; with (4.28)'s `g_{sl_i}(0)⁻¹ = (I,-p)` the off-diagonal signs also flip |
| N06 structure | p168 / 186 | Open chain with link frames `L_i` and inertias: `InertialChain n` (chain, `g_{sl_i}(0)`, `𝓜_i`); link pose `g_{sl_i}(θ) = e^{ξ̂₁θ₁}⋯e^{ξ̂ᵢθᵢ}g_{sl_i}(0)` | Link `k` frame moved by Lean joints `0..k`; `linkChain k` freezes later joints (twist `0`) | E009 `SerialChain`, `fk`, `jointMotions` | Verified: [I11](#implementation-evidence-i11); `InertialChain`, `InertialChain.linkChain`, `InertialChain.linkPose`, `InertialChain.linkPose_eq`, `InertialChain.linkPose_zero`; module `Dynamics/MassMatrix` | `𝓜_i` may be given in any body frame `L_i` (the kinetic-energy formula holds for the matching generalized inertia); the book places `L_i` at the mass center; the reading `g = g_{sl_i}(0)⁻¹` of the font-garbled (4.28) is an inference from the prose and the `J_i` display (E012 review F4); frame freedom of the link inertias has no library declaration yet, the reviewer's probe `reframe_massMatrix` is a candidate (F5) |
| N07 definition | p168 / 186 | Link body Jacobian `J_i = [ξ₁†⋯ξᵢ† 0⋯0]`, `ξⱼ† = Ad⁻¹_{(e^{ξ̂ⱼθⱼ}⋯e^{ξ̂ᵢθᵢ}g_{sl_i}(0))} ξⱼ`, and its 6×n matrix | Columns `Fin n → Twist`; rows `Twist.coordinates` | E009 `SerialChain.bodyJacobian` (eq3.55) of `linkChain k` | Verified: [I11](#implementation-evidence-i11); `InertialChain.linkBodyJacobian`, `InertialChain.linkBodyJacobian_of_le`, `InertialChain.linkBodyJacobian_of_lt`, `InertialChain.linkJacobianMatrix`, `InertialChain.linkJacobianMatrix_mulVec`, `RigidBody.coordinatesLinearMap` (+ `_apply`, `coordinates_add`, `_smul`, `_zero`, `_sum`, `_eq_zero_iff`) | None for the column formula; joint twists may be arbitrary (no unit premise) |
| N08 theorem | p168 / 186 | `Vᵇ_{sl_i} = J_i(θ)θ̇` for actual joint trajectories; the derivative exists | Actual `HasDerivAt` of each joint coordinate | E009 `SerialChain.bodyVelocity_fk`, `hasDerivAt_fk_toHomogeneous` | Verified: [I11](#implementation-evidence-i11); `InertialChain.bodyVelocity_linkPose`, `InertialChain.hasDerivAt_linkPose_toHomogeneous` | None |
| N09 definition | p168 / 186, eq4.18–4.19 | `M(θ) = Σ J_iᵀ 𝓜_i J_i` (`n×n`) and `T = ½θ̇ᵀMθ̇` | — | N07 | Verified: [I11](#implementation-evidence-i11); `InertialChain.massMatrix`, `InertialChain.kineticEnergy`, `InertialChain.massMatrix_apply`, `InertialChain.dotProduct_massMatrix_mulVec`, `dotProduct_transpose_mul_mul_mulVec` | None |
| N10 theorem | p168 / 186, eq4.17–4.18 | `T = Σᵢ Tᵢ`, `Tᵢ = ½(J_iθ̇)ᵀ𝓜ᵢ(J_iθ̇)`; with actual link body velocities | Actual derivatives of joints and link poses | N02, N08 | Verified: [I11](#implementation-evidence-i11); `InertialChain.kineticEnergy_eq_sum`, `InertialChain.kineticEnergy_eq_sum_bodyVelocity` | None |
| N11 theorem | p171 / 189, Lemma 4.2(1) | `M(θ)` symmetric for symmetric `𝓜_i`; PSD for PSD `𝓜_i` | Explicit hypotheses | N09 | Verified: [I11](#implementation-evidence-i11); `InertialChain.massMatrix_isSymm`, `InertialChain.massMatrix_posSemidef` | MLS states symmetric PD with no hypothesis on `𝓜_i` |
| N12 theorem | p171 / 189, Lemma 4.2(1) | `M(θ)` PD for PD `𝓜_i` and injective stacked Jacobian, and PD ⇔ stacked injective under PD `𝓜_i`; stacked injective at every `θ` when all joint twists are nonzero; hence PD at every `θ` for unit-axis revolute / unit-direction prismatic joints; `T = 0 ⇔ θ̇ = 0` | PD link inertias; nonzero twists or revolute/prismatic predicates | N09, N11, E009 `IsRevoluteJoint`/`IsPrismaticJoint` | Verified: [I11](#implementation-evidence-i11); `InertialChain.StackedJacobianInjective`, `InertialChain.massMatrix_posDef`, `_posDef_iff`, `InertialChain.stackedJacobianInjective_of_twist_ne_zero`, `InertialChain.massMatrix_posDef_of_twist_ne_zero`, `InertialChain.twist_ne_zero_of_isRevoluteJoint`, `_isPrismaticJoint`, `InertialChain.massMatrix_posDef_of_joints`, `InertialChain.kineticEnergy_eq_zero_iff` | The stacked-injectivity hypothesis is the assessment's inference, not printed in MLS; the nonzero-twist sufficiency is this increment's observation (triangular column structure), proved here |
| N13 definition | pp169–171 / 187–189, eq4.21–4.23 | Christoffel symbols `Γᵢⱼₖ`, Coriolis matrix `Cᵢⱼ = ΣΓᵢⱼₖθ̇ₖ`, `Ṁ = Σθ̇ₖ∂M/∂θₖ`, `(Cθ̇)ᵢ = ΣΓᵢⱼₖθ̇ⱼθ̇ₖ`; partials from Fréchet derivative data | Partial derivatives supplied as `dM : Fin n → Matrix` or read from `HasFDerivAt` entries (`partials`) | — | Verified: [I11](#implementation-evidence-i11); `Christoffel.symbol`, `Christoffel.coriolisMatrix`, `Christoffel.rate`, `Christoffel.rate_apply`, `Christoffel.coriolisMatrix_mulVec`, `Christoffel.partials`; module `Dynamics/Christoffel` | Derivative data are hypotheses/inputs, not computed for a general chain |
| N14 theorem | p171 / 189, Lemma 4.2(2) proof; p172 / 190 | `(Ṁ−2C)ᵢⱼ = Σ(∂ᵢMₖⱼ − ∂ⱼMᵢₖ)θ̇ₖ`; skew-symmetric when every `∂M/∂θₖ` is symmetric; `θ̇ᵀ(Ṁ−2C)θ̇ = 0` | Symmetric partial derivatives (stated explicitly) | N13 | Verified: [I11](#implementation-evidence-i11); `Christoffel.rate_sub_two_coriolisMatrix_apply`, `Christoffel.skew_rate_sub_two_coriolisMatrix`, `Christoffel.dotProduct_mulVec_eq_zero_of_transpose_eq_neg`, `Christoffel.dotProduct_rate_sub_two_coriolisMatrix_mulVec` | The printed "switching i and j" uses the symmetry of the partials implicitly; here it is a hypothesis |
| N15 theorem | p171 / 189, Lemma 4.2(2) | Along a trajectory: chain rule for `M(θ(t))`, symmetric partials from `M` symmetric everywhere, and `Ṁ−2C` skew for every actual derivative `Ṁ`; open-chain corollary | `M` symmetric at every configuration; `HasFDerivAt` of every entry at `θ(t)`; `HasDerivAt` of joint coordinates | N11, N13, N14; Mathlib `HasFDerivAt.comp_hasDerivAt`, `hasDerivAt_pi`, `HasFDerivAt.unique` | Verified: [I11](#implementation-evidence-i11); `Christoffel.hasDerivAt_comp`, `Christoffel.partials_isSymm`, `Christoffel.skew_deriv_sub_two_coriolisMatrix`, `InertialChain.skew_deriv_massMatrix_sub_two_coriolisMatrix` | For a general chain the differentiability of `M` is a hypothesis (not discharged; N21); discharged for the N16 arm |
| N16 specification | pp164–165 / 182–183, Fig4.4, eq4.10–4.11 | Planar two-link arm: link Jacobian columns, `M(θ)` equals printed (4.10) from the general (4.19); Christoffel `C` equals printed (4.11); `Ṁ−2C` computed and skew along every trajectory; `M(θ)` PD for positive masses and moments; `Examples/PlanarTwoLinkDynamics` | Arm along `+x` at `θ=0`; link frames at mass centers with base orientation; inertia `diag(Iᵢ)`; `I_zi = Iᵢ 2`; tool pose unused | N06–N15 | Verified: [I11](#implementation-evidence-i11); `Examples.twoLinkDynamicsChain`, `Examples.planarTwoLinkArm`, `Examples.planarTwoLinkArm_linkBodyJacobian_zero_zero`, `_zero_one`, `_one_zero`, `_one_one`, `Examples.planarTwoLinkArm_massMatrix`, `_massMatrix_posDef`, `_printedMassMatrix_posDef`, `Examples.planarTwoLinkArmMassDeriv`, `Examples.hasFDerivAt_planarTwoLinkArm_massMatrix`, `Examples.planarTwoLinkArm_coriolisMatrix`, `Examples.hasDerivAt_planarTwoLinkArm_massMatrix`, `Examples.planarTwoLinkArm_rate_sub_two_coriolisMatrix`, `Examples.planarTwoLinkArm_skew` | The book derives (4.10) from planar point kinematics; here it is derived from the PoE link Jacobians (independent route). PD needs `I_xi, I_yi > 0` too, although they do not appear in `M` |
| N17 definition (was: theorem) | p158 / 176, Theorem 4.1, eq4.5 | Lagrange's equations `d/dt ∂L/∂q̇ᵢ − ∂L/∂qᵢ = Υᵢ` as a predicate on a trajectory; `Dynamics/Lagrangian` | `L : ℝⁿ → ℝⁿ → ℝ` (configuration, velocity); partial derivatives are one-variable derivatives along coordinate lines; velocity `deriv θ`; the derivative of `s ↦ ∂L/∂q̇ᵢ(θ(s), θ̇(s))` must exist at `t` (part of the predicate) | — | Verified: [I12](#implementation-evidence-i12); `Lagrangian.velocityPartial`, `Lagrangian.positionPartial`, `Lagrangian.LagrangeEquationsAt`, `Lagrangian.LagrangeEquations` | The variational (or d'Alembert) derivation is not formalized: MLS cites [99] and gives no proof, so the predicate is the definition used. The row changes kind from theorem to definition. MLS reads `∂L/∂q̇` as row vectors; here every vector is `Fin n → ℝ` |
| N18 theorem | pp169–171 / 187–189, eq4.20–4.21, 4.24 | For `L = ½ q̇ᵀM(q)q̇ − V(q)`: Lagrange's equations at `t` ⇔ `M(θ)θ̈ + C(θ,θ̇)θ̇ + ∂V/∂θ = Υ`, with `C` the Christoffel matrix (4.23); (4.24) with `N = ∂V/∂θ + Nₑ`, `Υ = τ − Nₑ`; open-chain form; printed instances (4.11) and (4.7) | `M(q)` symmetric at every configuration; Fréchet derivatives of the entries of `M` and of `V` at `θ(t)`; near `t` the trajectory has velocity `θ'(s)` (actual derivatives), and `θ'` has derivative `θ''` at `t` | N13–N15, N17; for chains N21 (discharges the derivative hypotheses) | Verified: [I12](#implementation-evidence-i12); `Lagrangian.mechanical`, `Lagrangian.gradient`, `Lagrangian.apply_eq_dotProduct_gradient`, `Lagrangian.velocityPartial_mechanical`, `Lagrangian.positionPartial_mechanical`, `Lagrangian.hasDerivAt_mulVec`, `Christoffel.coriolisMatrix_mulVec_eq_rate_mulVec_sub`, `Lagrangian.lagrangeEquationsAt_mechanical_iff`, `Lagrangian.lagrangeEquationsAt_mechanical_iff_torque`, `InertialChain.lagrangian`, `InertialChain.lagrangian_apply`, `InertialChain.lagrangeEquationsAt_iff`, `InertialChain.lagrangeEquationsAt_potentialEnergy_iff`; printed instances `Examples.planarTwoLinkArm_lagrangeEquationsAt_iff` (4.11) and `Examples.sphericalPendulum_lagrangian`, `Examples.sphericalPendulum_lagrangeEquationsAt_iff` (4.7) | MLS asks for no explicit regularity; the formal statement needs only first derivatives of `M` and `V` at `θ(t)`, differentiability of `θ` near `t` and of `θ̇` at `t` (no `C²` hypothesis). Symmetry of `M` everywhere is a hypothesis (for chains it follows from symmetric link inertias, N11). The rearrangement into Christoffel symbols uses no symmetry of the partials |
| N19 definition | p169 / 187, pp174–175 / 192–193, eq4.25 | Potential energy `V(θ) = ∑ₖ mₖ g hₖ(θ)`, heights `hₖ = ⟪up, pₖ(θ)⟫` of the link-frame origins; gravity term `N(θ) = ∂V/∂θ` (gradient of the Fréchet derivative); its Jacobian form `∑ₖ mₖ g ⟪up, ωᵢₖ × pₖ + vᵢₖ⟫`; differentiability of `V` for every chain; Example 4.3's (4.25) | Uniform gravity, scalar `g`, upward vector `up` (gravity `−g·up`); link frame at the mass center (p168); masses an explicit argument | N06, N08 (E009 `hasDerivAt_fk_translation`), N21 | Verified: [I12](#implementation-evidence-i12); `InertialChain.linkHeight`, `InertialChain.potentialEnergy`, `InertialChain.gravityTerm`, `InertialChain.gravityTerm_eq_gradient`, `InertialChain.gravityJacobian`, `InertialChain.hasDerivAt_linkHeight`, `InertialChain.hasDerivAt_potentialEnergy`, `InertialChain.gravityTerm_eq_gravityJacobian`, `InertialChain.gravityTerm_eq_gravityJacobian_everywhere`, `InertialChain.differentiable_linkHeight`, `InertialChain.differentiable_potentialEnergy`, `InertialChain.lagrangeEquationsAt_gravity_iff`; printed instance `Examples.elbowChain`, `Examples.threeLinkArm`, `Examples.elbowChain_twist_coordinates`, `Examples.threeLinkArm_linkHeight`, `Examples.threeLinkArm_potentialEnergy`, `Examples.threeLinkArm_gravityTerm` (Example 4.3, heights p174, (4.25)); horizontal planar arm `Examples.planarTwoLinkArm_potentialEnergy_zAxis`, `Examples.planarTwoLinkArm_gravityTerm_zAxis` | Friction and other joint forces in `N` (p170) enter only through `Nₑ` in N18's torque form; no friction model is defined. The masses are not tied by type to the generalized inertias. Observation (consistency check, not an errata judgment): the printed (4.25), p175, shows the second entry as `−(m₂gr₁ + m₃gl₁) cos θ₂ − m₃r₂ cos(θ₂+θ₃))`, without `g` in the last term and with an unbalanced parenthesis; the derivative of the heights printed on p174 carries `g`, and that is what is formalized. The Prop. 4.9 caution (`N(q_d,0) ≠ 0`) concerns later use of `N` and is unchanged. The planar arm of Fig. 4.4 is treated by MLS as horizontal (`L = T`, p165); no printed gravity formula exists for it |
| N20 theorem | pp165–167 / 183–185, eq4.12–4.16 | Newton–Euler in body coordinates `𝓜V̇ᵇ + (ωᵇ×mvᵇ, ωᵇ×𝓘ωᵇ) = Fᵇ` as a predicate on a body-velocity curve (and on pose trajectories through the derivative-based body velocity); (4.14)/(4.15) as its components; coadjoint form `𝓜V̇ − ad_Vᵀ(𝓜V) = F`; power balance `d/dt ½Vᵀ𝓜V = Fᵇ·Vᵇ`; a satisfying instance | Body frame at the mass center; wrench at the mass center in body coordinates; body acceleration as actual derivatives of the linear and angular parts (the `Twist` carrier has no topology); `𝓘` symmetric for the power balance | N01, N02, `Wrench`, `Twist.bracket` (L-rows) | Verified: [I12](#implementation-evidence-i12); `RigidBody.inertiaAct`, `RigidBody.momentum`, `RigidBody.coordinates_momentum`, `RigidBody.gyroscopic`, `RigidBody.NewtonEulerEquation`, `RigidBody.newtonEulerEquation_iff`, `RigidBody.NewtonEuler`, `RigidBody.bodyVelocityCurve`, `RigidBody.coadjoint`, `RigidBody.pair_coadjoint`, `RigidBody.adMatrix`, `RigidBody.adMatrix_mulVec`, `RigidBody.coordinates_coadjoint`, `RigidBody.gyroscopic_eq_neg_coadjoint`, `RigidBody.coordinates_gyroscopic`, `RigidBody.pair_gyroscopic_self`, `RigidBody.hasDerivAt_kineticEnergy`, `RigidBody.hasDerivAt_kineticEnergy_of_newtonEulerEquation`, `RigidBody.NewtonEuler.hasDerivAt_kineticEnergy`, `RigidBody.newtonEuler_exp_zAxis` | (4.16) is the definition; the derivation from (4.12)–(4.13) on pp166–167 (inertial-frame Newton and Euler equations) is not formalized. The coadjoint form and the power balance are derivations in the library's conventions, not printed in MLS. The spatial form (Exercises 4–5) is not formalized. The instance (torque-free spin about a principal axis through the mass center) is illustrative, not a printed example |
| N21 theorem | pp175–177 / 193–195, eq4.26–4.30, Prop4.3 | (a) differentiability of every entry of the assembled `M(θ)` for every chain, discharging N15's derivative hypothesis and N18's for chains; (b) `Aₗⱼ` of (4.27), Jacobian columns `Ad_{g_{sl_l}(0)⁻¹} Aₗⱼ ξⱼ`, and `Mᵢⱼ = ∑_{l≥max(i,j)} (Aₗᵢξᵢ)ᵀ𝓜'ₗ(Aₗⱼξⱼ)` of (4.29) with `𝓜'ₗ` of (4.28); (c) the bracket formula (4.30) for `∂Mᵢⱼ/∂θₖ` | Arbitrary joint twists, reference link poses, link inertias; `Aₗⱼ` represented by the rigid motion `relativeMotion l j θ` for `j ≤ l` | N09, N13–N15, `Twist.exp`, `Twist.hat_adjoint`, Mathlib `Ring.inverse` differentiability | Unverified as a whole row; parts (a) and (b) Verified: [I12](#implementation-evidence-i12); `InertialChain.differentiable_linkBodyJacobian_coordinates`, `InertialChain.differentiable_massMatrix`, `InertialChain.massMatrixDeriv`, `InertialChain.hasFDerivAt_massMatrix`, `InertialChain.skew_deriv_sub_two_coriolisMatrix_massMatrixDeriv`, `InertialChain.relativeMotion`, `InertialChain.linkBodyJacobian_eq_adjoint_relativeMotion`, `InertialChain.massMatrix_apply_relativeMotion`; part (c) open | Only first-order differentiability is proved (no `C²` or smoothness claim). (4.30) is not formalized; the partial derivatives are available as Fréchet derivatives (`massMatrixDeriv`), not in bracket form. MLS's `Aₗⱼ = 0` for `l < j` is not represented; the sum is restricted to `l ≥ max(i,j)` |
| N22 definition | pp161–163 / 179–181, Ex4.2 | Inertia tensor as `-∫ρ r̂² dV`, centre of mass, Example 4.2 bar inertia; positivity from a nonnegative density | Measure-theoretic mass distribution | Mathlib integration | Unverified (open) | — |
| N23 specification | pp172–178 / 190–196, Ex4.3, Ex4.4 | Three-link (elbow) and SCARA inertia and Coriolis matrices | As printed | N16 pattern, N21 | Unverified (open) | Ex4.4's transformed-inertia display: see N05 observation |
| N24 theorem | p172 / 190; p209 / 227, Exercise 8 | Passivity: along solutions `Ḣ = θ̇·Υ` for `H = T + V`; conservation for `Υ = 0`; for chains in gravity with no derivative hypothesis on the model | Same as N18; for chains symmetric link inertias only | N14, N15, N18, N21 | Verified: [I12](#implementation-evidence-i12); `Lagrangian.energy`, `Lagrangian.hasDerivAt_energy`, `Lagrangian.hasDerivAt_energy_of_force_eq_zero`, `InertialChain.hasDerivAt_energy`, `InertialChain.hasDerivAt_energy_gravity` | Exercise 8 (read this session) states \"if `Ṁ − 2C` is skew-symmetric, then energy is conserved, i.e. `Ḣ = θ̇·τ`\"; the formal statement is that power balance with the generalized force `Υ` (`= τ` without friction), using the skew identity of N14 |
| N25 definition | p179 / 197, eq4.31 | Solutions of `ẋ = f(x, t)` from `t₀`, equilibria `f(x*, t) ≡ 0`, the constant solution at an equilibrium, restriction to later initial times, the shift of the equilibrium to the origin and its effect on solutions and on stability; `Control/Stability` | `f : ℝ → E → E` time first (MLS `f(x, t)`), `E` any real normed space; a solution is continuous on `[t₀, ∞)` with actual derivative `f t (x t)` at every `t > t₀` | Mathlib `HasDerivAt`, `ContinuousOn` | Verified: [I14](#implementation-evidence-i14); `Stability.IsSolution`, `Stability.IsEquilibrium`, `Stability.IsEquilibrium.isSolution_const`, `Stability.IsSolution.mono`, `Stability.shift`, `Stability.isSolution_shift_iff`, `Stability.stableAt_shift_iff` | MLS assumes existence and uniqueness (Lipschitz `f`); nothing here proves either. Every stability notion quantifies over all solutions, so statements hold whether or not solutions exist; non-vacuity is shown only by the equilibrium solution. Carathéodory solutions of a `t`-discontinuous `f` (MLS allows piecewise continuity) are not covered |
| N26 definition | pp179–180 / 197–198, Def4.1, eq4.32 | Stability in the sense of Lyapunov at `t₀` of a point `xe`; uniform stability (δ independent of `t₀ ≥ 0`); uniform implies pointwise; `Control/Stability` | Quantified over every solution from `t₀`; norms are the ambient norm | N25 | Verified: [I14](#implementation-evidence-i14); `Stability.StableAt`, `Stability.UniformlyStable`, `Stability.UniformlyStable.stableAt` | MLS states Definition 4.1 at `x* = 0`; here at any `xe`, equivalent by `stableAt_shift_iff` |
| N27 definition | p180 / 198, Def4.2, eq4.33 | Asymptotic stability at `t₀`; uniform asymptotic stability; uniform implies pointwise; `Control/Stability` | Uniform attractivity read as: one `δ`, and for each `η` a time `T` independent of `t₀ ≥ 0` and of the solution | N26 | Verified: [I14](#implementation-evidence-i14); `Stability.AsymptoticallyStableAt`, `Stability.UniformlyAsymptoticallyStable`, `Stability.UniformlyAsymptoticallyStable.asymptoticallyStableAt` | MLS states "the convergence in (4.33) is uniform" in words; the formal reading (uniform in `t₀` and the initial state) is the standard one, a choice of this increment |
| N28 definition | pp180–181 / 198–199, Def4.3, eq4.34 | Exponential stability and its global form; global implies local; exponential implies stability and asymptotic stability at every `t₀ ≥ 0`; `Control/Stability` | Constants `m, α, ε` independent of `t₀ ≥ 0` | N26, N27; Mathlib `Real.exp`, `Real.tendsto_exp_atBot` | Verified: [I14](#implementation-evidence-i14); `Stability.ExponentiallyStable`, `Stability.GloballyExponentiallyStable`, `Stability.GloballyExponentiallyStable.exponentiallyStable`, `Stability.ExponentiallyStable.stableAt`, `Stability.ExponentiallyStable.asymptoticallyStableAt` | MLS does not say how `t₀` is quantified in (4.34); uniform constants follow its remark that exponential stability implies uniform asymptotic stability (p181). That remark's "uniform" part is not formalized; the rate of convergence (largest `α`) is not defined |
| N29 definition | p182 / 200, Defs4.4–4.6, eq4.35–4.36 | Locally positive definite, positive definite and decrescent functions; the comparison functions; the derivative of `V` along the trajectories in a region and the formula `V̇ = ∂V/∂t + ∂V/∂x f`; `Control/Stability` | `V : ℝ → E → ℝ` time first; times `t ≥ 0`; comparison functions continuous, strictly increasing on `[0, ∞)` and zero at `0` (`IsClassK`); `V̇` is a hypothesis "`HasDerivAlongSolutions f V Vdot U`" | N25; Mathlib `HasFDerivAt.comp_hasDerivAt` | Verified: [I14](#implementation-evidence-i14); `Stability.IsClassK`, `Stability.IsClassK.pos`, `Stability.IsClassK.le`, `Stability.isClassK_mul_sq` (in PDControl), `Stability.LocallyPositiveDefinite`, `Stability.PositiveDefinite`, `Stability.Decrescent`, `Stability.HasDerivAlongSolutions`, `Stability.HasDerivAlongSolutions.mono`, `Stability.hasDerivAlongSolutions_of_hasFDerivAt` | MLS omits `α(0) = 0`; without it `α(r) = r − 1` makes `V ≡ 0` locally positive definite and Theorem 4.4(1) false for every unstable system, so the condition is added (Vidyasagar and Khalil, cited by MLS, include it). Definition 4.5 keeps the words "conditions of Definition 4.4" with a ball; the formal pdf has the bound for all `x` (the reading under which `α(p) → ∞` has content). `PositiveDefinite` is defined and not used |
| N30 theorem | p182 / 200, Thm4.4(1)–(2) | (1) lpdf `V` with `V̇ ≤ 0` on a ball for all `t ≥ 0` ⇒ the origin is stable at every `t₀ ≥ 0`; (2) with `V` also decrescent ⇒ uniformly stable; the trapping and monotonicity steps as lemmas; `Control/Stability` | As N29; proof by the first exit time from a ball (closed set, `sInf`) and monotonicity from `V̇ ≤ 0` | N25–N29; Mathlib `antitoneOn_of_hasDerivWithinAt_nonpos`, `IsClosed.csInf_mem`, `closure_Ico` | Verified: [I14](#implementation-evidence-i14); `Stability.antitoneOn_of_isSolution`, `Stability.norm_lt_of_lyapunov`, `Stability.stableAt_of_lyapunov`, `Stability.uniformlyStable_of_lyapunov`; instance on `ẋ = −x` in the gate's `Instances.lean` | MLS also assumes `V` non-negative; not needed. MLS gives no proof (it cites [118], [49]); the proof here is the standard one |
| N31 theorem | p183 / 201, Thm4.4(3), Table4.1 | lpdf and decrescent `V`, `−V̇` lpdf ⇒ the origin is uniformly asymptotically stable; hence asymptotically stable at every `t₀ ≥ 0`; `Control/Stability` | As N29; `−V̇` lpdf includes continuity of `V̇` (as MLS's definition requires) | N27, N30 | Verified: [I14](#implementation-evidence-i14); `Stability.uniformlyAsymptoticallyStable_of_lyapunov`; instance on `ẋ = −x` in the gate's `Instances.lean` | None beyond N27's reading of uniform convergence |
| N32 theorem | p183 / 201, Thm4.4(4), Table4.1 | pdf, decrescent `V`, `−V̇` pdf ⇒ global uniform asymptotic stability | — | N29, N31 | Unverified (open) | — |
| N33 theorem | pp183–184 / 201–202, Thm4.5 | Exponential stability ⇔ quadratic bounds `α₁‖x‖² ≤ V ≤ α₂‖x‖²`, `V̇ ≤ −α₃‖x‖²`, `‖∂V/∂x‖ ≤ α₄‖x‖` near 0; rate bounds `m ≤ (α₂/α₁)^{1/2}`, `α ≥ α₃/(2α₂)` (p184); global version | `V` continuous on `ℝ₊ × E`; bounds for all `x` and `t ≥ 0` | N28, N29; Mathlib `Real.sqrt`, `Real.exp` | Unverified as a whole row; sufficiency in the global form with the printed rate bounds Verified: [I14](#implementation-evidence-i14); `Stability.norm_le_of_quadratic_lyapunov`, `Stability.globallyExponentiallyStable_of_quadratic_lyapunov`; instance on `ẋ = −x`; open: the local form (`‖x‖ ≤ ε`) and the converse | The `α₄` bound is used only by the converse and is not assumed |
| N34 theorem | pp184–185 / 202–203, Thm4.6, eq4.37–4.40 | Stability by linearization; eigenvalue criterion for time-invariant systems | — | Mathlib spectra and matrix exponential (adequacy at the pin not assessed) | Unverified (open) | — |
| N35 specification | pp185–189 / 203–207, Ex4.5–4.7 | Damped harmonic oscillator (energy fails, skewed energy gives exponential stability), nonlinear spring with damper (stability, then Lasalle) | As printed | N30, N33, N36 | Unverified (open) | Not instantiated. Observation: Example 4.5's `Mq̈ + Bq̇ + Kq = 0` is `Control.errorField` with `n = 1`, `K_p = K/M`, `K_v = B/M` after division by `M > 0`, so N39's `globallyExponentiallyStable_errorField` covers its conclusion; the instance is not written |
| N36 theorem | pp188–189 / 206–207, Defs4.7–4.8, Thm4.7 | ω-limit sets, invariant sets, Lasalle's principle for autonomous systems | Needs existence, uniqueness and continuous dependence | N25 | Unverified (open) | — |
| N37 definition | p190 / 208, eq4.47; pp169–172 / 187–190 | The manipulator model `M(θ)θ̈ + C(θ, θ̇)θ̇ + N(θ, θ̇) = τ` with `N = ∂V/∂θ + Nₑ`; the equations of motion as Lagrange's equations with generalized force `τ − Nₑ` and their equivalence with (4.47); the power balance `Ṫ = θ̇ ⬝ (τ − N)`; the first-order closed-loop field under a feedback law `u(t, θ, θ̇)`; the equivalence of its solutions with motions satisfying (4.47); rest points `(q, 0)` ⇔ `u(t, q, 0) = N(q, 0)`; `Control/ManipulatorSystem` | `ManipulatorModel n` = `InertialChain n` + masses, `g`, `up`, `Nₑ(θ, θ̇)`; state `(θ, θ̇) ∈ ℝⁿ × ℝⁿ` (sup norm); `f(t, (q, v)) = (v, M(q)⁻¹(u − C v − N))` with Mathlib's `Matrix.inv`; symmetric link inertias; `M(q)` positive definite for every `q` where the inverse is used | N18, N19, N21, N24, N25; supporting lemmas `Control.hasDerivAt_dotProduct`, `Control.hasDerivAt_mulVec_const`, `Control.PosDef.mulVec_inv_mulVec`, `Control.PosDef.inv_mulVec_mulVec` | Verified: [I14](#implementation-evidence-i14); `ManipulatorModel`, `ManipulatorModel.M`, `.C`, `.N`, `.lagrangian`, `.EquationsOfMotionAt`, `.equationsOfMotionAt_iff`, `.hasDerivAt_kineticEnergy`, `.field`, `.eventually_hasDerivAt_fst`, `.equationsOfMotionAt_of_isSolution`, `.isSolution_of_equationsOfMotionAt`, `.isEquilibrium_field_iff`, `.continuous_M` (in PDControl) | MLS assumes arbitrary joint torques can be commanded (p189); no actuator limits, sampling or model error. The masses are not tied by type to the generalized inertias (as N19). `M(q)` positive definite is a hypothesis (MLS Lemma 4.2(1) asserts it; N12 discharges it for revolute and prismatic chains with PD link inertias) |
| N38 theorem | pp190–191 / 208–209, eq4.48–4.50 | Computed torque law (4.49); under it (4.47) holds at `t` ⇔ `ë + K_v ė + K_p e = 0` at `t` (with `K_p = K_v = 0` this is (4.48)); every closed-loop solution gives an error `(e, ė)` solving `d/dt(e, ė) = (ė, −K_v ė − K_p e)`; `Control/ComputedTorque`, `Control/ErrorDynamics` | Desired trajectory with actual derivatives `θ_d'`, `θ_d''` at every time; `M(θ(t))` (resp. every `M(q)`) positive definite; no gain hypothesis for the algebra | N37 | Verified: [I14](#implementation-evidence-i14); `ManipulatorModel.computedTorque`, `ManipulatorModel.equationsOfMotionAt_computedTorque_iff`, `Control.errorField`, `ManipulatorModel.isSolution_errorField` | None for the algebra; MLS's "uniformly positive definite" (p191) is used only as invertibility |
| N39 theorem | p192 / 210, Prop4.8 | `K_p, K_v` symmetric positive definite ⇒ exponential trajectory tracking: `∃ m, α > 0` depending only on the gains with `‖(e(t), ė(t))‖ ≤ m e^{−α(t−t₀)}‖(e(t₀), ė(t₀))‖` for every closed-loop solution from `t₀ ≥ 0` (state-space and Lagrange forms); the error system is globally exponentially stable; planar two-link instance; `Control/ErrorDynamics`, `Control/ComputedTorque`, `Control/QuadraticBounds` | Gains: Mathlib `PosDef` (symmetric by definition); sup norm on `ℝⁿ × ℝⁿ`; exact model cancellation | N28, N33, N38; compactness bounds `QuadraticBounds.*` | Verified: [I14](#implementation-evidence-i14); `Control.skewedEnergy`, `Control.skewedEnergyRate`, `Control.hasDerivAlongSolutions_skewedEnergy`, `Control.exists_skewedEnergy_bounds`, `Control.globallyExponentiallyStable_errorField`, `ManipulatorModel.computedTorque_tracking`, `ManipulatorModel.computedTorque_tracking_of_equationsOfMotionAt`, `QuadraticBounds.exists_pos_mul_sq_norm_le`, `.exists_le_mul_sq_norm`, `.exists_pos_mul_sq_norm_le_of_continuous`, `.exists_le_mul_sq_norm_of_continuous`, `.exists_pos_mul_sq_norm_le_dotProduct_mulVec`, `.posDef_exists_pos_mul_sq_norm_le`, `.exists_pos_mul_dotProduct_mulVec_le`, `.exists_dotProduct_mulVec_le_mul_sq_norm`; instance `Examples.planarTwoLinkModel`, `Examples.planarTwoLinkModel_M`, `Examples.planarTwoLinkArm_computedTorque_tracking` | Different route from the printed proof: MLS shows the eigenvalues of `A = [[0, I], [−K_p, −K_v]]` have negative real part (and uses, without proof, that this gives exponential decay); here the skewed energy of Example 4.5 (p186) and Theorem 4.5 sufficiency (N33) are used, and no eigenvalue statement is formalized. Constants are not explicit (compactness) |
| N40 theorem | pp193–195 / 211–213, Prop4.9, eq4.51–4.52; p195 / 213 | (a) the printed caution: under the bare PD law (4.51) with constant `θ_d`, `(θ_d, 0)` is a rest point of (4.47) ⇔ `N(θ_d, 0) = 0`, with a formal counterexample on Example 4.3's arm in gravity; (b) PD with compensation of `N` (`τ = N(θ, θ̇) − K_v θ̇ − K_p e`, (4.53) with `θ̇_d ≡ 0`): closed loop (4.52), `V = ½θ̇ᵀMθ̇ + ½eᵀK_p e` has `V̇ = −θ̇ᵀK_vθ̇`, `(θ_d, 0)` is an equilibrium and is Lyapunov stable; (c) asymptotic (global) stability, the printed conclusion; `Control/PDControl`, `Examples/ThreeLinkGravityPD`, `Examples/PlanarTwoLinkControl` | Symmetric link inertias; `M(q)` PD for every `q`; `K_p` symmetric PD; `K_v` PSD suffices for (b) (MLS: `K_v > 0`) | N30, N37; (c) needs N36 | Unverified as a whole row; parts (a) and (b) Verified: [I14](#implementation-evidence-i14); (a) `ManipulatorModel.pdTorque`, `.equationsOfMotionAt_const_iff`, `.equationsOfMotionAt_const_pdTorque_iff`, `.isEquilibrium_pdTorque_iff`, `Examples.threeLinkModel`, `Examples.threeLinkArm_not_equilibrium_pd`; (b) `ManipulatorModel.pdCompensatedTorque`, `.pdEnergy`, `.hasDerivAt_pdEnergy`, `.isEquilibrium_pdCompensatedTorque`, `.stableAt_pdCompensatedTorque`, supporting `Control.dotProduct_mulVec_comm`, `Control.sq_norm_prod_le`; instance `Examples.planarTwoLinkArm_linkInertia_isSymm`, `Examples.planarTwoLinkArm_stableAt_pdCompensatedTorque`; (c) open | Source observation (formal counterexample, not an errata judgment): the printed Proposition 4.9 applies (4.51) to (4.47), but its proof's closed loop (4.52) omits `N`; for (4.47) with `N(θ_d, 0) ≠ 0` the point `θ = θ_d` is not an equilibrium (`threeLinkArm_not_equilibrium_pd`: Example 4.3's arm, `g ≠ 0`, `m₂r₁ + m₃l₁ + m₃r₂ ≠ 0`, any gains). The p195 sentence "(4.53) simplifies to the original PD control law (4.51)" for `θ̇_d ≡ 0` drops the `N` term of (4.53). The printed statement holds as written when `N(θ_d, 0) = 0` (for example gravity- and friction-free); the formal version adds compensation of `N`, which is (4.53) at `θ̇_d ≡ 0`. The proof's "For `θ_d ≡ 0`" reads as a misprint for `θ̇_d ≡ 0` (rendered p193). Only Lyapunov stability is proved; the asymptotic conclusion needs Lasalle (N36); global statements are not addressed |
| N41 theorem | pp194–195 / 212–213, eq4.53–4.54, Prop4.10 | Augmented PD law (4.53): exponential tracking via `V = ½ėᵀMė + ½eᵀK_pe + εeᵀMė` | — | N33, N37; bounds on `M` and its derivatives along the trajectory | Unverified (open) | Not attempted. Observation (inference, not checked formally): `V̇` contains terms `ε eᵀ(Ṁ − C)ė` that are cubic in the error, so the printed "negative definite for ε small" needs bounds on `M`, `∂M` and the desired trajectory and gives at most a local result; the set-point case is N40(b) |
| N42 theorem | pp195–199 / 213–217, eq4.55, Lemma4.11, Ex4.8 | Workspace dynamics `M̃ẍ + C̃ẋ + Ñ = F` for an invertible parametrization `f`; Lemma 4.11 (`M̃` symmetric PD, `M̃˙ − 2C̃` skew); workspace computed torque and PD | Smooth invertible `f`, `n = p` | N37–N40, Chapter 3 Jacobians | Unverified (open) | Example 4.8 is a numerical illustration (Figures 4.10–4.11), not a formal obligation. The text extraction of the p198 workspace computed-torque law shows `C(θ, θ̇)ẋ + N(θ, θ̇)` without tildes; not checked against a rendering |

[E016](../../docs/implogs/E016-controllers-and-lyapunov-stability.md) adds 18 selected obligations N25-N42 from Chapter 4 §4-5, printed pp. 179-199 (PDF 197-217); modules [Stability](../../RoboLean/Control/Stability.lean), [QuadraticBounds](../../RoboLean/Control/QuadraticBounds.lean), [ManipulatorSystem](../../RoboLean/Control/ManipulatorSystem.lean), [ErrorDynamics](../../RoboLean/Control/ErrorDynamics.lean), [ComputedTorque](../../RoboLean/Control/ComputedTorque.lean), [PDControl](../../RoboLean/Control/PDControl.lean), and the instance files [PlanarTwoLinkControl](../../RoboLean/Examples/PlanarTwoLinkControl.lean) and [ThreeLinkGravityPD](../../RoboLean/Examples/ThreeLinkGravityPD.lean).

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
| P3 kinematics | Ch3 pp81-154; P1/P2 | K01-K16 (I7, I10) and the design rows C01-C07 | K17-K26 ([I13](#implementation-evidence-i13)): Paden-Kahan Subproblems 1-3, singular configurations with Examples 3.11 and 3.13, closed-chain structure equation, its differential and `ρ`; K27–K30 ([I16](#implementation-evidence-i16)): Example 3.12, the elbow manipulator (Examples 3.2 and 3.5), manipulability and `W′_D`, the planar inverse kinematics (3.16); Gruebler, redundancy and further examples un-inventoried |
| P4 energy/dynamics | Ch4 pp155-178; P2/P3 | N01-N16 (I11): generalized inertia and its frame change, link Jacobians and the mass matrix with symmetry, PSD and PD under explicit hypotheses, Christoffel symbols and the skew identity, the planar two-link example | N17-N24 open: Theorem 4.1, Euler-Lagrange assembly, potential energy and gravity, Newton-Euler, Prop4.3 differentiability of M, mass integrals, further examples, passivity |
| P5 trajectories/control | Ch4 pp179-207; P4/analysis | None | Solution regularity, Lyapunov, exact-model control; resolve Proposition 4.9 gravity-term caution; N25-N42 ([I14](#implementation-evidence-i14)): Lyapunov definitions, Theorems 4.4(1)-(3) and 4.5 (global sufficiency), the manipulator closed loop, Proposition 4.8 in full and 4.9 in part; open N32, N34-N36, N41, N42 |
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

## Implementation evidence I9

E010, the `Twist` carrier change ([entry](../../docs/implogs/E010-twist-structure.md)), recorded by root at 2026-10-09 10:08:14 UTC. `Twist` is an `@[ext]` two-field structure with fields `linear` and `angular` on the `Wrench` pattern; `Twist.linear` and `Twist.angular` are projections; no norm, metric or topology is declared. No row changes status. The lead's [statement diff](../../docs/implogs/gates/E010/20261009T092849Z/statement-diff.txt) and [notation-free check](../../docs/implogs/gates/E010/20261009T092849Z/literal-only-check.txt) show 0 removed names, 36 added (25 hand-written with p. 41 docstrings, 11 generated by the structure command) and 38 statement texts that differ only by a pair literal becoming a twist literal; the rows concerned are listed in the [proposal](../../docs/implogs/gates/E010/20261009T092849Z/ledger-and-conventions-proposal.md). I8's sentence "`Twist` remains `Vec3 × Vec3`" is superseded. **Verified — integrated gate:** [gate](../../docs/implogs/gates/E010/20261009T100204Z/) records `lake build` exit 0 in 23 s with no warning on the 60-module root (the two I10 modules included) and the whole-library audit with 1701 constants, only `propext`, `Classical.choice` and `Quot.sound`, no `sorryAx`; all 64 sources unchanged during the gate. Type separation is Verified by the lead's [probe](../../docs/implogs/gates/E010/20261009T092849Z/TypeSeparation.lean), re-run by root against the lead's shadow (exit 0; 20 `#check_failure` lines fail, including the absent `Norm Twist` and `Dist Twist` instances). Physical fidelity, numerics and user acceptance remain Unverified.

## Implementation evidence I10

E011 ([entry](../../docs/implogs/E011-planar-workspace-certificate-and-force-pullback.md)), recorded by root at 2026-10-09 10:08:14 UTC: new modules [ForcePullback](../../RoboLean/Kinematics/ForcePullback.lean) (K13) and [PlanarTwoLinkWorkspace](../../RoboLean/Examples/PlanarTwoLinkWorkspace.lean) (C01–C07). Sources read by the lead as text extracts: printed pp. 62–63, 95, 96–97 and 121 and the assessment paragraph ([extracts](../../docs/implogs/gates/E011/20261009T093129Z/source/)). Lead evidence: both files elaborate with exit 0 and no warning ([ForcePullback](../../docs/implogs/gates/E011/20261009T093129Z/check-ForcePullback.out), [PlanarTwoLinkWorkspace](../../docs/implogs/gates/E011/20261009T093129Z/check-PlanarTwoLinkWorkspace.out)); the [axiom audit](../../docs/implogs/gates/E011/20261009T093129Z/axioms.out) prints 28 ordered rows for the 28 public declarations, each exactly the three standard axioms ([verifier](../../docs/implogs/gates/E011/20261009T093129Z/axioms-verify.txt)); [instances](../../docs/implogs/gates/E011/20261009T093129Z/Instances.lean) exit 0 (planar torques matching the first two rows of Example 3.10's transpose on p. 122; reachability of concrete points; the origin cases). **Verified — integrated gate:** the [E010/E011 gate](../../docs/implogs/gates/E010/20261009T100204Z/) built both modules against the `Twist` structure in the 60-module `lake build` (exit 0, no warning) and the whole-library audit lists their 17 and 26 constants with only the three standard axioms. I10 marks K13 Verified in full: 123 of the 126 selected MLS obligations are Verified in full; R27, R28 and X60 (partial) remain. C01–C07 are design rows outside that count, all seven Verified by the same gate. Not formalized: the frictionless-work premise and time integral, the non-square-Jacobian caveat of p. 121, uniqueness or continuity of the planar inverse kinematics, Jacobian rank. Physical fidelity, numerics and user acceptance remain Unverified.

## Implementation evidence I11

E012 ([entry](../../docs/implogs/E012-rigid-body-inertia-and-mass-matrix.md)), recorded by root at 2026-10-09 10:11:43 UTC: the first Chapter 4 tranche in four new modules, rows N01–N16 above; N17–N24 are inventoried and open. Sources read by the lead as text extracts with printed pp. 162, 168, 176 and 177 rendered ([extracts](../../docs/implogs/gates/E012/20261009T092904Z/source/), [plan](../../docs/implogs/gates/E012/20261009T092904Z/plan.md)). Lead evidence: the four modules elaborate with exit 0 and no output against a shadow copy of the pre-E010 library ([checks](../../docs/implogs/gates/E012/20261009T092904Z/checks/)); the ordered [axiom audit](../../docs/implogs/gates/E012/20261009T092904Z/axiom-audit.out) prints the three standard axioms for all 89 named declarations and a sweep over all 156 constants of the four modules finds none outside them; the printed (4.10) and (4.11) matrices are reproduced from the general formula (4.19) through link Jacobians. **Verified — integrated gate:** [gate](../../docs/implogs/gates/E012/20261009T100913Z/) records `lake build` exit 0 in 11 s with no warning on the 64-module root, built against the `Twist` structure of I9, and the whole-library audit with 1857 constants (RigidBodyInertia 40, MassMatrix 60, Christoffel 19, PlanarTwoLinkDynamics 37), only `propext`, `Classical.choice` and `Quot.sound`, no `sorryAx`; all 68 sources unchanged during the gate. Hypotheses are explicit throughout: symmetry and positivity of the inertia tensor are assumed, not derived from a density; the stacked-Jacobian injectivity behind positive definiteness is the assessment's inference, with the new sufficiency result that nonzero joint twists give injectivity everywhere; differentiability of a general chain's `M` is a hypothesis (N21 open) and is discharged for the planar arm. Source observation recorded in N05: the Example 4.4 display on p. 177 is not the product of its own displayed factors. Physical realizability of inertial parameters, numerics and user acceptance remain Unverified.

## Implementation evidence I12

E013 ([entry](../../docs/implogs/E013-lagrangian-dynamics-and-newton-euler.md)): Chapter 4
tranche 2, in the new modules [Lagrangian](../../RoboLean/Dynamics/Lagrangian.lean),
[PotentialEnergy](../../RoboLean/Dynamics/PotentialEnergy.lean),
[NewtonEuler](../../RoboLean/Dynamics/NewtonEuler.lean) and
[MassMatrixDerivative](../../RoboLean/Dynamics/MassMatrixDerivative.lean), with the printed-example
files [PlanarTwoLinkLagrangian](../../RoboLean/Examples/PlanarTwoLinkLagrangian.lean) ((4.11) from
Lagrange's equations with `L = T`; zero potential and gravity term for `up = +z`, a consistency check),
[ThreeLinkGravity](../../RoboLean/Examples/ThreeLinkGravity.lean) (Example 4.3: the printed twist
coordinates of p172, the heights of p174 and their derivative, which is (4.25) with `g` restored in
the last term of the second entry) and [SphericalPendulum](../../RoboLean/Examples/SphericalPendulum.lean)
(Example 4.1: the printed `L` of p160 and (4.7) from the general theorem). The example files are
evidence for N18 and N19, not separate obligations; each is one instance. Sources read by the lead as
text extracts, with printed p. 175 rendered
([extracts](../../docs/implogs/gates/E013/20261010T002511Z/source/)). **Verified - lead evidence:**
every module elaborates with exit 0 and no output against a shadow copy of the built library, and
the ordered [axiom audit](../../docs/implogs/gates/E013/20261010T002511Z/axiom-audit.out) prints only
the three standard axioms for all 75 public declarations; the
[instances](../../docs/implogs/gates/E013/20261010T002511Z/Instances.lean) (exit 0) show a pendulum
hanging at rest satisfying Lagrange's equations with zero force and the hypothesis-free chain theorem
applied along a constant trajectory. **Verified - root's integrated gate
[E013/20261010T005937Z](../../docs/implogs/gates/E013/20261010T005937Z/):** `lake build` exit 0 in
9 s with 0 warnings on the 71-module root (2850 jobs), each of the seven modules reported as built;
whole-library audit `modules=71 constants=2029 standard_three=1888 axiom_free=14 disallowed=0
opaque=0 axiom_decls=0`; commit `f042580`. Hypotheses are explicit: Lagrange's equations are a
predicate (MLS cites the proof); `M` symmetric at every configuration; first-order derivative data,
discharged for every chain by the differentiability of `M` and `V`; gravity uniform with an explicit
up vector and link frames at the mass centers; symmetric `𝓘` for the Newton-Euler power balance.
Not formalized: the variational derivation of Theorem 4.1, the derivation of (4.16) from
(4.12)-(4.13), the bracket formula (4.30), friction models. Source observation recorded in N19: the
(4.25) display on p. 175 omits `g` in one term. I12 marks N17, N18, N19, N20 and N24 Verified and
N21 partial: 144 of the 150 rows through I11. Physical fidelity, numerics and user acceptance remain
Unverified.

## Implementation evidence I13

E014 ([entry](../../docs/implogs/E014-inverse-kinematics-subproblems-and-singularities.md)):
new modules [PadenKahan](../../RoboLean/Kinematics/PadenKahan.lean),
[Singularity](../../RoboLean/Kinematics/Singularity.lean),
[ClosedChain](../../RoboLean/Kinematics/ClosedChain.lean) and
[PlanarTwoLinkSingularity](../../RoboLean/Examples/PlanarTwoLinkSingularity.lean). Sources
read by the lead as text extracts: printed pp. 97-104 and 122-135
([extracts](../../docs/implogs/gates/E014/20261010T002522Z/source/)). **Verified - lead
evidence:** each module elaborates in a shadow tree of the built oleans with exit 0 and no
output ([checks](../../docs/implogs/gates/E014/20261010T002522Z/)); the ordered
[axiom audit](../../docs/implogs/gates/E014/20261010T002522Z/axioms.out) prints exactly the
three standard axioms for all 88 public declarations
([verifier](../../docs/implogs/gates/E014/20261010T002522Z/axioms-verify.txt)), and the
[sweep](../../docs/implogs/gates/E014/20261010T002522Z/axiom-sweep.out) over all 152 constants
of the four modules finds none outside them; the
[instances](../../docs/implogs/gates/E014/20261010T002522Z/Instances.lean) satisfy the
hypotheses of the subproblem, singularity and closed-chain theorems on concrete inputs
(exit 0); the same checks re-run against root's E015 build
([rerun](../../docs/implogs/gates/E014/20261010T005608Z/)) give the same results.
**Verified - root's integrated gate
[E014/20261010T010046Z](../../docs/implogs/gates/E014/20261010T010046Z/):** `lake build` exit 0
in 6 s with 0 warnings on the 75-module root (2857 jobs), the four modules reported as built;
whole-library audit `modules=75 constants=2181 standard_three=2019 axiom_free=14 disallowed=0
opaque=0 axiom_decls=0`; commit `fc99877`. Hypotheses the book does not state are named in the
K17-K19 divergence cells. Source observation: for the planar two-link arm the p123 definition
gives no singular configuration when `a ≠ 0`; the folded configurations are singular for the
position map only (K23, C08). I13 adds 13 selected rows K17-K29, of which K17-K26 are Verified
in full and K27-K29 open, and the design row C08 (Verified, counted separately): 163 selected,
154 Verified in full. Physical fidelity, numerics and user acceptance remain Unverified.

## Implementation evidence I14

E016 ([entry](../../docs/implogs/E016-controllers-and-lyapunov-stability.md)): roadmap P5 tranche 1,
Chapter 4 §4–5, in the new modules [Stability](../../RoboLean/Control/Stability.lean),
[QuadraticBounds](../../RoboLean/Control/QuadraticBounds.lean),
[ManipulatorSystem](../../RoboLean/Control/ManipulatorSystem.lean),
[ErrorDynamics](../../RoboLean/Control/ErrorDynamics.lean),
[PDControl](../../RoboLean/Control/PDControl.lean) and
[ComputedTorque](../../RoboLean/Control/ComputedTorque.lean), with the instance files
[PlanarTwoLinkControl](../../RoboLean/Examples/PlanarTwoLinkControl.lean) (the planar two-link arm
meets every hypothesis of Propositions 4.8 and 4.9 as formalized, `K_p = K_v = I`) and
[ThreeLinkGravityPD](../../RoboLean/Examples/ThreeLinkGravityPD.lean) (Example 4.3's arm in
gravity: under the bare PD law (4.51), `θ = θ_d = 0` is not a rest point). Sources read by the lead
as text extracts of printed pp. 179–199, with pp. 182, 191, 193 and 194 rendered
([extracts](../../docs/implogs/gates/E016/20261010T013200Z/source/)). **Verified - lead evidence:**
every module elaborates with exit 0 and no output against a shadow copy of root's post-E017 build
([checks](../../docs/implogs/gates/E016/20261010T013200Z/checks/)); the
[axiom audit](../../docs/implogs/gates/E016/20261010T013200Z/axiom-audit.stdout) over all 170
constants of the eight modules reports `disallowed=0 opaque=0 axiom_decls=0`, and the ordered
[`#print axioms`](../../docs/implogs/gates/E016/20261010T013200Z/print-axioms-verify.txt) over the
95 hand-written public declarations prints exactly the three standard axioms for each; the
[instances](../../docs/implogs/gates/E016/20261010T013200Z/Instances.lean) (exit 0) satisfy the
hypotheses of Theorems 4.4(1)–(3) and 4.5 on `ẋ = −x` and give a closed-loop solution of the
planar arm under compensated PD. Hypotheses the book does not state: `α(0) = 0` for comparison
functions; `M(q)` positive definite as an explicit hypothesis; compensation of `N` in the PD
law. Not formalized: existence and uniqueness of solutions, Theorem 4.4(4), the local form and the
converse of Theorem 4.5, Theorem 4.6, Lasalle (Theorem 4.7), asymptotic stability of PD control,
Proposition 4.10, workspace control. Source observation recorded in N40: Proposition 4.9 as
printed fails for (4.47) with `N(θ_d, 0) ≠ 0` (formal counterexample). I14 adds 18 selected rows
N25–N42: 181 selected, 164 Verified in full. Physical fidelity, numerics and user acceptance remain
Unverified. **Verified - root's integrated gate [E016/20261010T020417Z](../../docs/implogs/gates/E016/20261010T020417Z/):** `lake build` exit 0 in 14 s with 0 warnings on the 83-module root (2872 jobs), each of the eight modules reported as built; whole-library audit `modules=83 constants=2352 standard_three=2174 axiom_free=14 disallowed=0 opaque=0 axiom_decls=0`; commit `70fcc3b`.

## Implementation evidence I15

E018 ([entry](../../docs/implogs/E018-veil-pilot-planar-arm-supervisor.md)): the Veil pilot. New
Lean module [PlanarArmSupervisor](../../RoboLean/Design/PlanarArmSupervisor.lean) (rows C09,
C10), added to the root import list by root at landing (see the integrated-gate sentence below); new Veil files `Examples/RoboLean/PlanarArmSupervisor.lean`
and `PlanarArmSupervisorUnsafe.lean` in the sibling project `robo-lean-veil` (Veil 0263f6c, Lean
4.32.0). Sources read by the lead as text extracts of printed pp. 95 and 98
([extracts](../../docs/implogs/gates/E018/20261010T212023Z/source/)). **Verified - lead
evidence:** the module elaborates with `lake env lean` exit 0 and no output; the ordered
[`#print axioms`](../../docs/implogs/gates/E018/20261010T212023Z/print-axioms.stdout) over its 21
public declarations (with structure fields and constructors) prints no axiom outside
`propext`, `Classical.choice`, `Quot.sound`, and the sweep over the 39 constants of
`RoboLean.Design` reports `outside_standard_three=0 sorryAx=0 axiom_decls=0 opaque=0`; the
[instances](../../docs/implogs/gates/E018/20261010T212023Z/Instances.lean) (exit 0) give a
reachable state with `(0, 2, 0)` commanded for `a = 2`, `b = 1`, a rejection of the origin, and
the five-target guard table of the Veil instance. **Veil side, recorded as Veil's report:** with
`veil.smt.trust false`, `#model_check interpreted` "✅ No violation (explored 768 states)" on the
five-target instance with no depth bound; four `sat trace` queries "✅ Satisfying trace found";
`unsat trace` over exactly six actions silent with exit 0; `#check_invariants` ✅ on all ten
rows; `#print axioms` on the ten generated theorems prints only the three standard axioms, and a
control with trust on shows `sorryAx` in exactly the five SMT-discharged ones; the deliberately
unsafe variant reports "❌ Violation" from the model checker, a counterexample to the `unsat
trace` and ❌ on `admit`/`commanded_reachable`
([gate](../../docs/implogs/gates/E018/20261010T212023Z/)). The Veil-to-Lean correspondence is a
recorded convention, not a kernel link. **Verified - root's integrated gate [E020/20261010T215401Z](../../docs/implogs/gates/E020/20261010T215401Z/):** `lake build` exit 0 in 48 s with 0 warnings on the 87-module root (3110 jobs), run in a linked worktree holding HEAD `d2d0b53` plus the E018 and E020 files (byte-identical to the committed ones; `.lake/packages` shared with the main checkout, Mathlib reported current), because the main working tree held other leads' partial edits; whole-library audit `modules=87 constants=2528 standard_three=2311 axiom_free=44 disallowed=0 opaque=0 axiom_decls=0`; commits `9c8b539` (E018) and `c2a2604` (E020). Physical fidelity, the sampled implementation, numerics and user acceptance
remain Unverified.

## Implementation evidence I16

E020 ([entry](../../docs/implogs/E020-chapter-3-remainder-inverse-kinematics-and-manipulability.md)):
new modules [Manipulability](../../RoboLean/Kinematics/Manipulability.lean),
[PlanarTwoLinkInverseKinematics](../../RoboLean/Examples/PlanarTwoLinkInverseKinematics.lean) and
[ElbowManipulator](../../RoboLean/Examples/ElbowManipulator.lean); additions and the E014 lemma moves
in EulerAngles, TwistAdjoint, SerialChain, Workspace, Singularity, PadenKahan and
PlanarTwoLinkWorkspace. Sources read by the lead as text extracts of printed pp. 84, 89–91, 97–98,
104–106, 123–129, with pp. 89–90 rendered
([extracts](../../docs/implogs/gates/E020/20261010T211850Z/source/)). **Verified - lead evidence:**
all sixteen owned modules elaborate in dependency order in a shadow tree seeded from the built
oleans, each with exit 0 and no output
([checks](../../docs/implogs/gates/E020/20261010T211850Z/checks/summary.txt)); the ordered
[axiom audit](../../docs/implogs/gates/E020/20261010T211850Z/print-axioms.out) prints exactly the
three standard axioms for all 85 public declarations added or moved
([verifier](../../docs/implogs/gates/E020/20261010T211850Z/print-axioms-verify.txt)), and the
[sweep](../../docs/implogs/gates/E020/20261010T211850Z/axiom-sweep.out) over all 618 constants of the
sixteen modules finds none outside them, no `opaque` and no `axiom`; the
[instances](../../docs/implogs/gates/E020/20261010T211850Z/Instances.lean) (exit 0) satisfy the
hypotheses of the K27, K28, K29 and K30 theorems on concrete inputs. Hypotheses the book does not
state are named in the K28 and K30 divergence cells. Source observations: MLS p98's "if `α ≠ 0`,
there are two distinct values of `θ₂`" fails modulo `2π` at `α = π`; MLS p129's "`det J(θ)` is the
product of the singular values" holds for `|det J(θ)|`. I16 adds one selected row, K30
(182 selected), and moves K27–K30 to Verified (K28 Verified for the row as stated; the eight-solution count is not formalized): 182 selected, 168 Verified in full. Physical
fidelity, numerics and user acceptance remain Unverified. **Verified - root's integrated gate [E020/20261010T215401Z](../../docs/implogs/gates/E020/20261010T215401Z/):** `lake build` exit 0 in 48 s with 0 warnings on the 87-module root (3110 jobs), run in a linked worktree holding HEAD `d2d0b53` plus the E018 and E020 files (byte-identical to the committed ones; `.lake/packages` shared with the main checkout, Mathlib reported current), because the main working tree held other leads' partial edits; whole-library audit `modules=87 constants=2528 standard_three=2311 axiom_free=44 disallowed=0 opaque=0 axiom_decls=0`; commits `9c8b539` (E018) and `c2a2604` (E020).

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
