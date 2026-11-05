# Roadmap for a Lean library based on MLS

Date: 2026-10-08

The current status is under [Current state](#current-state) (2026-11-03); P0–P10 below remain a dependency roadmap, not blanket completion claims.

## Objective and scope

Translate most of the mathematical core of Murray, Li, and Sastry's *A Mathematical Introduction to Robotic Manipulation* into a reusable Lean library. The purpose is a baseline for several research directions: compositional modeling, robot design, control, planning, and learning. Workspace-defined design and STL monitors are examples, not the organizing limits of the project.

The initial coverage target is Chapters 2–8, relevant foundations in Appendix A, and mathematical specifications for the computational operations in Appendix B. Chapters 1 and 9 supply context rather than a substantial theorem backlog. Exercises should be selected when they establish reusable results or expose important cases; reproducing every exercise is not an agreed requirement.

The book has been surveyed and selected central arguments inspected, not exhaustively audited. The [coverage ledger](mls-coverage-ledger.md) makes selected obligations of Chapters 2–6, the first parts of Chapters 7 and 8 and Appendix A explicit; it is not yet an exhaustive inventory of the book. “Most” should eventually be measured against the expanded ledger, with omissions and changed hypotheses recorded explicitly.

Read the [research assessment](mls-lean-assessment.md) for chapter-level evidence and the [Veil assessment](veil-robotics-verification.md) for transition-system verification. Textbook page references use printed pages in MLS.pdf; main-text printed page N is PDF page N+18.

## Current state

Status 2026-11-03: the library at commit `852f931` and the [coverage ledger](mls-coverage-ledger.md) with the rows V01–V22 (commit `6342e10`), W01–W21 (`66b2eb0`), L05–L32 (`c2bad4e`), R29–R30, T16–T18, X64, N44–N46, H31 (`1af10d8`), K42–K64 (`5931e69`), V24–V25 and the design row C29 (`8b52cdc`), H32–H38 and N50–N55 (`af52a71`), K65–K69 and L34–L35 with N46 and H31 completed to Verified in full (`11f25b2`), W23–W29 with W15, W19 and W20 completed to Verified in full (`acffbdf`), L60–L72 (`70996af`), G73–G83, R31–R39, T19–T20 and X65 (`ff247f7`), V26–V35 with V18 completed to Verified in full (`a574f74`), N56–N60 and H39–H41 (`4dcf7f7`), G90–G100 (`f3ff57a`), K70–K81 (`5a14b34`), V40–V43 and W30–W39 (`f083494`), L80–L82 and G101–G105 with L71 completed to Verified in full (`b38c1e7`), V50–V55 and W45–W47 with V14 completed to Verified in full (`70613b9`), V60–V75 and W60–W62 (`75c5b45`), K82–K96 (`d862d82`), V76–V79, V84–V85 and W70–W74 (`ae9b863`), V80–V83 and G110 with V10 and G90 completed to Verified in full (`a2a55d2`), and V90–V96 and G120–G124 (`852f931`). The toolchain is Lean 4.34.1 with Mathlib v4.34.1, pinned in `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`. **Verified - formal checking:** `lake build` of the 430 modules imported by `RoboLean.lean` succeeds, and a whole-library axiom audit of those modules reports 11367 constants, each depending on at most `propext`, `Classical.choice` and `Quot.sound`, with no `axiom` declaration and no `opaque` stand-in. The ledger counts 596 selected MLS obligations, 580 of them Verified in full (G40, L72, W30, W47 and V85 assessment rows; W28 and V75 named statements, not proved; K94 and K95 open; V11, L28, L29, K76, V43, V78 and W74 partial), and twenty-nine design rows C01–C29 separately (C25 and C27 tested, not proved; C26 a Veil-side check; C29, differentiable dependence on initial conditions, kernel-checked). These are selected obligations, not independent theorem counts or a whole-book percentage, and the work packages below remain a dependency plan rather than completion claims. The [repository README](../../README.md) links every module.

- **P0, ledger and conventions:** the ledger holds selected rows for Chapters 2–8 and Appendix A (the twist bracket, the matrix-group examples and section 3.2, the metric properties of `SE(3)`) with their assumptions, changed hypotheses and source observations, and the [geometry conventions](geometry-conventions.md) record the coordinate and sign choices; in Chapters 7 and 8 a completeness pass (rows V60–V75 and W60–W62) compared the printed items outside the exercises with the rows, and the exercises and informal parts that no row selects are listed in the backlog notes V23 and W22 of the ledger; Appendix A's manifold statements and Appendix B are not inventoried.
- **P1, rigid transforms:** rows R01–R11 and T01–T15 are Verified: proper rigid transforms, composition, inverses and point and vector actions, distance and cross-product preservation, and the equivalence with homogeneous matrices. Rows T16–T18 (commit `1af10d8`) add the converse of Definition 2.1 for maps of `ℝ³` and the planar group `SE(2)` with Exercise 11. Rows R31–R39, T19–T20 and X65 (commit `ff247f7`) add Exercises 3, 6(e), 7, 9(a)–(c) and 16, Example 2.1, the ZYX remark of p. 33 at both `θ = ±π/2` and the nonexistence of a global chart of `SO(3)`. Frame-indexed types remain open.
- **P2, twists, exponentials and wrench duality:** rows R07–R30, X01–X64 and L01–L04 are Verified (R29, R30 and X64 with commit `1af10d8`), including the quaternion rotation map with its double cover and the common normal of two screw axes constructed so that the reciprocal product (2.72) covers every pair of nonparallel finite screws, with parallel and infinite-pitch cases stated apart.
- **Appendix A foundations:** rows L05–L32 (commit `c2bad4e`; L28 and L29 partial, L33 a backlog note): frame-invariant metrics on `ℝⁿ`, `Ad`-invariant forms on `se(3)` with Lemma A.4, Proposition A.5 and Corollary A.5.1 for forms extended by left translation, the hyperbolic metric and the Killing form with Examples A.21–A.23, Exercise 2.17, Examples A.26–A.27, Proposition A.1, the Lie algebras of matrix groups from left invariant fields, exponentials and canonical coordinates on `GL(n)`, Examples A.12–A.13 and A.15–A.18; rows L34–L35 (commit `11f25b2`) add Theorem A.8 for volume forms on `se(3)` extended by left translation and the log function of Examples A.14–A.15 as the inverse of `exp`; rows L60–L72 (commit `70996af`; L71 completed by rows L80–L82 below, L72 an assessment): the Lie algebras and dimensions of `GL(n)`, `SO(n)` and `SE(3)` at matrix level, translations and `X_L(G) ≅ T_eG`, one-parameter subgroups and the logarithm of `SO(3)` near the identity, `GL(n)` as a Lie group in Mathlib's sense with the commutator as its bracket, one-forms, the volume `8π²` of `SO(3)` in exponential coordinates and Proposition A.7 as printed; rows L80–L82 (commit `b38c1e7`; L71 to Verified in full) add the derivative of the exponential chart of `SO(3)` with its Jacobians `A(ω)` and `A(ω)ᵀ`, and the volume as the total mass of a measure in exponential coordinates, invariant under conjugation; the manifold statements, Proposition A.6, Proposition A.7 for its intended notion and Theorem A.9 remain open.
- **P3, manipulator kinematics:** rows K01–K41 and the design rows C01–C07 are Verified: product-of-exponentials kinematics, spatial and body Jacobians with their derivative form (3.51)–(3.55), force pullback, workspaces, Paden–Kahan Subproblems 1–3, singular configurations, the closed-chain structure equation, manipulability, the elbow manipulator with its eight solutions under regularity hypotheses, the planar inverse kinematics (3.16), the smoothness of the forward kinematics of every order, Gruebler's formula at the velocity level, parallel mechanisms of `k` chains with kinematic and actuator singularities, self-motions with Example 3.17 and the four-bar linkage's uncertainty configuration, with a workspace certificate for the planar two-link arm. Rows K42–K64 (commit `5931e69`) add the Denavit–Hartenberg form (3.6)–(3.10), base frames and reference configurations, the SCARA of Examples 3.1, 3.3, 3.6 and 3.10, Example 3.4's workspaces, resolved rates (3.57) under added hypotheses, the Stanford arm's Jacobian (3.58), minimum-norm rates and the statics (3.63), the spherical joint and the Stewart platform's structure equation (3.72), leg Jacobian (3.73) and coplanar actuator singularity, and Exercises 5–8 and 13–22 in part. Rows K65–K69 (commit `11f25b2`) add the ZYZ endpoint cases, three-axis angles onto `SO(3)`, the spherical-wrist workspace with the elbow manipulator as an instance, the count of Subproblem 4's three spheres and Exercise 13(b)–(c). Rows K70–K81 (commit `5a14b34`) add the slider–crank, the variable geometry truss and the U-joint Stewart platform of Exercises 20–22 with their structure equations and singularities, and the forward kinematics and Jacobians of the four manipulators of Figure 3.23 with the inverse kinematics of three. Rows K82–K96 (commit `d862d82`) add Exercise 4 for the four manipulators of Figure 3.24 (the inverse elbow and the Rhino with singular families, the Stanford arm's inverse kinematics through Subproblem 5 and the elbow manipulator's spatial Jacobian), Exercise 3(b)–(c) for Figure 3.23(ii), the elbow with non-intersecting shoulder axes (Exercise 5), the SCARA's extension (Exercise 7) and Exercises 10 and 12, with the truss's kinematic singularity at one leg of zero length in K76; Exercise 1, the singular value decomposition of Exercises 9 and 11, the body Jacobians, remaining singularities and workspaces of Figure 3.24's manipulators and two legs of zero length (K76) remain.
- **P4, energy and open-chain dynamics:** rows N01–N24 are Verified: generalized inertia, the mass matrix with symmetry and definiteness under explicit hypotheses, Christoffel symbols and the skew identity, Lagrange's and the Newton–Euler equations, potential energy and gravity, the inertia tensor, passivity and the printed matrices of Examples 4.3 and 4.4. Rows N50–N55 (commit `af52a71`) add Euler's equation in spatial coordinates, the derivation of (4.14)–(4.16) from (4.12)–(4.13), Exercises 1, 3 and 5 and viscous friction. Rows N56–N60 (commit `4dcf7f7`) derive (4.8)–(4.9) from the volume integral of a mass distribution, with the generalized inertia of a body frame anywhere, compute the inertia tensors of the homogeneous ellipsoid and cylinder of Exercise 2, and derive Exercise 3 and the parallel-axis theorem from the mass integrals; Exercise 6 is H15.
- **P5, trajectories, stability and controllers:** rows N25–N43 are Verified: the Lyapunov definitions, Definition 4.3's bound with named constants and its arrival time, Theorems 4.4–4.7 (the converse of Theorem 4.5 with all four bounds for fields with a continuous bounded derivative, through differentiable dependence on initial conditions (design row C29), and under a hypothesis structure for a solution flow differentiable in the initial state; Theorem 4.6 for continuous `A(t)`), computed torque, PD and augmented PD control for the manipulator and for every robot `(M, C, N)`, exponential set-point regulation under PD with compensation of `N` on bounded sets of initial errors, workspace dynamics with Lemma 4.11, workspace computed torque and the workspace PD laws including Exercise 9, and Examples 4.5–4.7; rows N44–N46 (commit `1af10d8`) add Chapter 4 §6: the constrained dynamics (4.56)–(4.62) with Lemma 4.2 for (4.62), the hybrid position/force law (4.63) with its closed loop and exponential tracking, and the slot of §6.3 through Exercise 12(b) and (d) (the printed elbow-down parameterization with its Jacobian and Exercise 12(c) added by commit `11f25b2`). The fourth bound for fields that are only Lipschitz and Theorem 4.6 for `A(t)` with jumps (Carathéodory solutions are not adopted) are open.
- **P6, grasp and contact kinematics:** rows G01–G72 are Verified (G40 an assessment row, G41 and G61 backlog notes): contact models, friction cones, grasp maps, force-closure with Propositions 5.1–5.3, internal forces, the hand Jacobian and the grasping constraint, manipulability and Table 5.4, grasp planning with Theorems 5.4–5.6 and Theorem 5.7 assessed (rows G73–G83, commit `ff247f7`: its "only if" in a torsional form and for coplanar normals, the printed "only if" false at every torsional coefficient, the line and plane contacts of Exercise 4 and Exercises 1, 2(a), 2(b), 3(b), 8(c) and 9), and rolling contact (surface charts, the Gauss frame, the geometric parameters, Lemma 5.10, the contact coordinates, Theorem 5.11, Corollary 5.11.1, Proposition 5.12 for two chart patches, the grasp kinematics with rolling (5.40)–(5.41) with hands with rolling contacts, Examples 5.6–5.7 and Exercises 13, 14, 15 (two equal axes), 16 and 17), and rows G90–G100 (commit `f3ff57a`): Theorem 5.9 as a named statement, proved since commit `a2a55d2` (G90, G110), with its flow-free steps (charts along lines of curvature without umbilics are orthogonal; the principal frame away from umbilics), the curvature tensor of level sets (Exercise 19), the three-axis ellipsoid of Exercises 14–15 in confocal coordinates, and the contact set of two whole bodies with the change of chart and the transfer of Theorem 5.11. Rows G101–G105 (commit `b38c1e7`) add Exercises 5(b) (the regular tetrahedron), 8(a) (the trapezoid), 2(c) (the sphere), 11 (the SCARA fingertip) and 12 (fingertip locations for every hand). Rows G120–G124 (commit `852f931`) add the coverage of the confocal patch, the excluded confocal points as umbilics, Theorem 5.11 across a change of the object chart, and the frame angle of a change of chart with a derivative. Table 5.3, Chapter 5 Exercises 2(d), 3(a), 5(a), 5(c)–(d), 10 and 18, a chart along lines of curvature and a chart-free form of the contact kinematics for level sets are open.
- **P7, constrained dynamics and composition:** rows H01–H25 and H27–H30 are Verified: Pfaffian constraints, multipliers and the Lagrange–d'Alembert equations with Examples 6.1–6.2, the substituted Lagrangian (6.15), the hand–object system (6.16)–(6.28) with Lemma 6.1, a chart of `SE(3)` with (6.23), redundant manipulators and grasps with Example 6.3, tendons with Examples 6.4–6.5, the hand torques (6.36), and the `attach` and `control` operations on robots with Lemma 6.1 for `attach` and Example 6.7 as a one-dimensional toy; H31 (commits `1af10d8` and `11f25b2`) is Exercise 7, the wall, including (b) with point masses. Rows H32–H38 (commit `af52a71`) add the nonmanipulable grasps with (6.33) derived from (6.32) and the left pseudo-inverse, the implicit finger configuration of `attach`, redundant fingers in `attach`, the net payload force and Exercises 1 and 3. Rows H39–H41 (commit `4dcf7f7`) add §3.3's two-fingered SCARA grasp with the conditions for manipulability and no internal motions, Exercise 5 (the four-bar linkage in its crank angle) and Exercise 6 (the tendon networks, rigid and elastic) under recorded readings of the figures.
- **P8, nonholonomic analysis:** rows V01–V22 (commit `6342e10`): vector fields, Lie derivatives and the Lie bracket with the book's sign and its relation to the matrix commutator and the twist bracket, Proposition 7.1, distributions and the generator criterion, the Lie algebra `L(g)` and its rank, (7.9) with the necessity half of Theorem 7.2, Proposition 7.4 ("only if"), drift-free systems with piecewise constant inputs, reachable sets and small-time local controllability, Exercise 4 and the reversal step of Proposition 7.7, the filtration with Definitions 7.2–7.3 and Exercises 10–11 (11 under the module form of `Δᵢ₊₁ = Δᵢ`), and Examples 7.2/7.7, 7.4/7.9, 7.5/7.10 and 7.6/7.11 with growth vectors, degrees, the rank condition and nonholonomy. Rows V24–V25 (commit `8b52cdc`): flows of fields with a bounded continuous derivative with the group property, each `φ^X_t` a diffeomorphism, and commuting flows with the square (7.8) closing exactly for a vanishing bracket. Rows V26–V35 (commit `a574f74`): local frames, the flow of class `C¹` in time and state, composed flows and the flow box, (7.9) with `C^n` defining maps, flows commuting where the bracket vanishes, Theorem 7.2 "if" with `C¹` defining maps on finite-dimensional spaces, Proposition 7.3 near a point, Proposition 7.4 "if" near each point, Exercise 11 from equal ranks of a regular filtration, and the Philip Hall basis with Example 7.12. The sufficiency half of Theorem 7.2 with smooth defining maps is proved on finite-dimensional spaces, from flows of class `C^k` in the initial state for every `k` (rows V10 and V80–V83, commit `a2a55d2`); Theorem 7.5 is proved on finite-dimensional spaces with controllability from the rank condition (rows V14 and V50–V55, commit `70613b9`). Rows V40–V43 (commit `f083494`): nilpotency of p. 344, Exercise 2 for `ρ ≠ 0`, Exercise 16, and Exercise 17 at stages 1–3 (stages `i ≥ 4` and the attainment of the stage-3 bound by (8.6) open). Rows V60–V75 (commit `75c5b45`), a completeness pass over pp. 317–347 outside the exercises: level sets of integrals of the constraints, (7.4)–(7.6), the involutive closure, the Lie algebra of smooth fields, codistributions with `Δ = Ω^⊥`, Proposition 7.3 on the whole space in the book's normal form, Examples 7.3 and 7.8 corrected, integrals annihilating `L(g)`, the existence of the degree of nonholonomy, and Example 7.12's spanning and independence halves with the basis property for every `m` a named statement; Proposition 7.3 for arbitrary one-forms on the whole space is open. Rows V76–V79, V84 and V85 (commit `ae9b863`): Exercise 1 under smoothness and a regular filtration, Exercise 6's trailer equations, Exercise 12 at matrix level, Exercise 13's falling cat with a first integral, Exercise 14's Philip Hall basis of order 5, and Exercise 15's degree assessed at `N = 0`. Rows V90–V96 (commit `852f931`): the involutive closure involutive and integrable where its rank is constant, the `n − rank Δ̄` integrals of pp. 339–341 (of class `C¹` and smooth) with the maximum number attained, and nilpotency on fields equal to nilpotency on formal products with Example 7.12 restated through it and a nonabelian instance.
- **P9, nonholonomic steering:** rows W01–W21 (commit `66b2eb0`): Brockett's system with degree 2 and growth vector `(2, 3)` and the stationary inputs of (8.3) with the corrected `q₃(1)`, the `m`-input system (8.4)–(8.5), the one-chain system with Lemma 8.1, Proposition 8.2 and Proposition 8.3 (Algorithm 3 steers to every configuration), Algorithm 3's displacement `(a/4π)^k b/k!` for every `k` and the second-order formulas of p. 363 (every trajectory, every initial state, sinusoidal inputs), (8.11)–(8.16) with Proposition 8.4 under the necessary conditions (8.12)–(8.13) and Exercise 6's norm preservation, Engel's system, Example 8.3 as printed and corrected for (7.14), (8.30)–(8.31), (8.34)–(8.36), Theorem 8.6 for coordinate rectangles and the equation of Proposition 8.7. Rows W23–W29 and the completions of W15, W19, W20 (commit `acffbdf`): Exercise 6 in `SO(m)` with (8.17), Theorem 8.6 for chart regions between graphs over `v_f` and for the polar cap modulo `2π`, Proposition 8.7 by rolling around the kite of Figure 8.5, (8.6) for `m` inputs with the Jacobi relation and Algorithm 2's step 3 for any two inputs, Algorithm 1's step 2 for one pair of inputs of (8.4)–(8.5), the §3.2 distributions and conditions with the conversion to one-chain form proved from `h₁, h₂` and the existence of `h₂` a named statement, proved with a `C¹` `h₂` in dimension `n` and false as stated for other `n` (rows W46–W47, commit `70613b9`), and the one-chain system controllable by Chow's theorem (W45). the existence of a smooth `h₂` is proved in dimension `n` (W28, commit `a2a55d2`); Theorem 8.6 for regions bounded by general closed curves is open; the book's approximate methods (Examples 8.1–8.2, §4.2, Ritz, the Chen–Fliess series) are not selected. Rows W30–W39 (commit `f083494`): Exercise 1 as printed (not controllable, a first integral) and corrected (rank condition, growth vector `(2, 3, 5, 8)`, nilpotent of order 4), Exercise 2 (nilpotent of order 3), Exercise 3(a), Exercise 5(a)–(c), Exercises 7, 8, 9 and 11 by the method of Proposition 8.4, and Exercise 12; Exercises 3(b), 5(d) and 13–14 are open or not selected. Rows W60–W62 (commit `75c5b45`): Algorithm 1 steering (8.4)–(8.5) to every configuration, Example 8.2's change of coordinates and Engel's pendulum equation. Rows W70–W74 (commit `ae9b863`): Exercise 1's question answered for the corrected system under a change of coordinates, Exercise 3(c), Exercise 4's polynomial equations, Exercise 7's `u⁽ⁿ⁾`, and Exercise 10 up to (8.19). Theorem 8.6 for general closed curves is open.
- **P10, computational specifications:** the first increment is the [planar arm demo](planar-arm-demo.md) (design rows C19–C25, commit `b254787`): an executable supervisor over `ℚ` with core imports only, proved to refine the design supervisor, joined to a floating-point simulation loop whose integration and inverse kinematics are unverified. The executable also builds natively as the Lake target `planar-arm-supervisor` (commit `d8e99a5`), with the same answers as the interpreter on the protocol transcript. A differential test against Veil's executable semantics of the supervisor model (design rows C26–C27, commit `7975d6c`) agrees on all 16 225 states of 201 traces, a test rather than a proof. Arrival-time statements for the ideal continuous arm (design row C28, commit `5a650af`) join the executable's run invariants to an exponential bound on the end-effector error at each commanded set point, with explicit constants for the demo's parameters that certify arrival only for an age bound of `39 775 296` ticks, far above the demo's `18`. Evaluators for conversions, adjoints, exponentials, kinematics and Jacobians and floating-point error bounds are open.

## Three connected deliverables

1. **Mathematical library:** definitions and proved results about robot geometry, mechanics, and control.
2. **Modeling interface:** representations of components and assemblies, with theorems connecting generated expressions to mathematical semantics.
3. **Computational tools:** evaluators, numerical methods, or external certificates connected to specifications by correctness or approximation results.

These have different completion criteria. A real-valued existence theorem need not produce an algorithm. An executable algorithm need not have a numerical error theorem. A theorem about an ideal robot does not establish the parameters of a physical robot.

## Architecture choices to evaluate

| Choice | Initial proposal | Question for the prototype |
|---|---|---|
| Rigid transforms | Concrete matrices or rotation/translation pairs, with proved equivalence | Does this expose mathlib algebra while supporting later derivatives? |
| Frames and quantities | Distinct frames, points, vectors, twists, and wrenches | Which distinctions belong in type indices versus explicit predicates? |
| Coordinates | Declare composition direction, twist order `(v, ω)`, and spatial/body conventions | Can conversions be proved once and used without hidden sign changes? |
| Configuration spaces | Explicit coordinates and domains initially, retaining periodic/constrained structure where required | Which results are local, and which require a global manifold? |
| Robot description | A small assembly language with separately stated semantics | Do generated equations agree with an independently meaningful component model? |
| Generality | One worked mechanism and reusable lemmas, followed by a second example | Which abstractions actually earn their complexity? |

The first slice selects named rotation/translation fields, Mathlib's special orthogonal matrices, and EuclideanSpace coordinates, with an explicit homogeneous-matrix equivalence. The remaining choices are recommendations to test; this concrete representation does not settle the eventual manifold interface. Reuse mathlib foundations where appropriate rather than duplicating them just to match textbook notation.

## Work packages

This is a dependency plan, not a calendar estimate. Differential geometry is a supporting strand throughout. Computational certification can begin with a small operation once its mathematical specification exists.

### P0. Coverage ledger and conventions

Extend the [initial ledger](mls-coverage-ledger.md) with one row per selected definition, proposition, lemma, algorithm, or important equation. Record the book reference; intended Lean statement/module; assumptions and conventions; existing mathlib dependencies and missing bridges; proof status; and any changes to the printed claim.

Distinguish definitions from substantive equivalence theorems. Defining FK as a product of exponentials and unfolding it is not the same deliverable as proving agreement with joint-by-joint geometric semantics.

Maintain the [geometry conventions](geometry-conventions.md) for frame direction, composition order, handedness, twist/wrench ordering, units or dimensional conventions, and admissible joint coordinates. Include concrete examples that disambiguate the conventions.

### P1. Rigid transforms and frame composition

Source: Chapter 2, pp.23–38, and selected Appendix A material.

Reuse or connect to `SO(3)`; define rigid transformations, composition, inverses, and point/vector actions. Prove closure, inverse/action laws, distance/orientation preservation, and equivalence between pair and homogeneous-matrix representations. Evaluate frame-indexed composition.

A frame type can prevent mismatched composition. It cannot establish that a measured transform was assigned the truthful frame label.

### P2. Twists, exponentials, and wrench duality

Source: Chapter 2, pp.27–30 and 39–69; Appendix A. Depends on P1.

The checked subset includes hat/vee and cross-product covariance; hat powers and actual Rodrigues/exponential laws; unit-axis and rigid-exponential existence including identity and half-turn cases; elementary rotations, generic Z-Y-Z inverse coordinates, and selected principal coordinates with their domain and nonuniqueness limits. Twist carriers, matrix/coordinate brackets, adjoints, derivative-based velocities, independent screw-motion agreement, Chasles existence, and wrench power/work and reciprocal-space laws extend this foundation. Actual affine axes and finite/pure-translation/stationary cases are distinguished; scalar normalization changes the full twist and norm-based magnitude uses the absolute scalar. The [ledger](mls-coverage-ledger.md) identifies the exact Chapter 2 and selected Appendix A subset. Tangent/manifold interpretations of the coordinate bracket and remaining reciprocal-geometry cases are separate work.

Exponential surjectivity and a noncomputable selected coordinate reconstructing every rigid transform are checked separately. No global smooth or unique logarithm follows; signed axis/angle uniqueness has an interior principal-angle domain, half-turn axes have a sign ambiguity, and identity axes are not unique. A Euclidean norm on six twist coordinates is not invariant under every frame change; retain explicit metric and length-scale choices.

### P3. Manipulator kinematics

Source: Chapter 3, pp.81–154. Depends on P1/P2.

Represent reference poses, joints, and admissible configurations. Connect joint-motion composition to product-of-exponentials FK. Prove spatial/body Jacobians are the corresponding derivatives, establish their coordinate relation, and derive force pullback. Define workspace and dextrous workspace with explicit quantifiers.

Add selected Paden–Kahan subproblems with existence/branch conditions, singularity statements, and closed-chain constraints with required rank assumptions. Accompany general development with a two-link or SCARA example. Generalize to finite chains after exercising the representation and derivative interface.

Position reachability, pose reachability, a continuous IK selection, and feasible motion between configurations are distinct claims.

### P4. Energy and open-chain dynamics

Source: Chapter 4, pp.155–178. Depends on the needed P2/P3 results.

Define inertia and kinetic/potential energy with explicit physical assumptions; develop Lagrangian and Newton–Euler formulations and selected equivalences. Assemble link energies and the joint-space mass matrix. Prove symmetry, positive definiteness under actual nondegeneracy hypotheses, and skew symmetry of `dot M - 2 C` for the chosen Coriolis construction.

For `M = Σ Jᵢᵀ Iᵢ Jᵢ`, positive semidefinite inertias yield positive semidefiniteness. Strict positivity needs more: positive definite link inertias plus injectivity of the stacked Jacobian suffice. Physical realizability of inertial parameters is separate from matrix positivity alone.

### P5. Trajectories, stability, and controllers

Source: Chapter 4, pp.179–207; relevant analysis foundations. Depends on P4.

Build a trajectory/solution interface with time domains, regularity, and existence assumptions. Develop the Lyapunov and invariance results needed by selected controllers. Prove computed-torque and PD-family claims with explicit model, actuation, gain, and domain premises. Express controller theorems through reusable structural hypotheses where possible.

Resolve the apparent missing `N` assumption/compensation in printed Proposition 4.9 before adopting its statement; see the assessment. Distinguish local/global statements, stability/asymptotic/exponential convergence, and exact/uncertain models. Continuous-time controller theorems do not automatically cover sampled implementation.

### P6. Grasp and contact kinematics

Source: Chapter 5, pp.211–264. Can branch from P2/P3 without waiting for all of P5.

Formalize contact models, admissible force cones, grasp maps, internal forces, force closure, manipulability, finger/object compatibility, and rolling kinematics with smooth-surface/chart/curvature assumptions.

Keep maintained ideal contacts distinct from creation/loss of contact, impacts, and uncertainty. Force closure with unbounded force magnitudes does not establish feasibility under finite actuator limits.

### P7. Constrained dynamics and composition

Source: Chapter 6, pp.265–316. Depends on needed P4/P6 material.

Develop Pfaffian constraints, multipliers, Lagrange–d'Alembert dynamics, and conditions under which composite/reduced dynamics retain energy and inertia structure. Address redundancy/nonmanipulability explicitly. Formalize ideal tendon force maps and tension-only feasibility. Develop versions of the book's `attach` and `control` operations (pp.303–310).

Expose rank, compatibility, and contact premises. Do not infer closed-loop stability merely from stability of individual components. Ideal time-independent constraint reactions do zero power under their velocity constraint; numerical constraint solvers require a separate argument.

### P8. Nonholonomic structure and controllability

Source: Chapter 7, pp.317–354, supported by Appendix A and analysis foundations.

Develop or reuse vector fields, flows, distributions, brackets, integrability, and selected Frobenius/controllability results. Connect concrete robotic constraints to the abstract theorems through worked examples.

State smoothness, rank/domain, drift, and control-set hypotheses. The book's control-reversal argument requires appropriate signed controls. A local controllability rank condition is not a constructive steering algorithm. This foundational branch need not wait for every grasp/control application.

### P9. Nonholonomic steering

Source: Chapter 8, pp.355–394. Depends on P8 and relevant examples.

Cover selected sinusoidal and chained-form constructions, preconditions and coordinate transformations, approximation/error statements, and rolling-finger examples. Distinguish exact constructions from approximations.

General collision-free planning is outside the book's coverage. Controllability and steering formulas do not establish obstacle avoidance, actuator feasibility, or global optimality.

### P10. Computational specifications and certified execution

Source: Appendix B, pp.435–439, with further work for numerical guarantees.

Begin with conversions, adjoints, exponentials, FK, and Jacobians already specified mathematically. Choose a small executable representation and state its relation to the exact one. The ledger's specification notes B01–B05 map every function documented in Appendix B (`Screws.m` and `RobotLinks.m`) to the library declaration that specifies it; they are the targets of such evaluators and are not book obligations.

Possible routes include exact finite/rational computation, symbolic expressions, certified approximation, and independently checked external certificates. The choice is open. Continuous energy conservation does not establish an integrator's conservation, and a proof over `ℝ` does not certify external floating-point code.

## First implementation slice

The first increment established rigid-transform foundations; later increments extend rotation representations, geometric screws, velocities, brackets, and wrench/work interfaces. The ledger identifies the exact checked subset. Continue in this order:

1. Inspect the ledger's status and evidence.
2. Review the written rigid-transform statements and concrete examples against the conventions; user acceptance remains separate from the compiled proofs.
3. Address the remaining rigid-motion obligations before claiming all of P1: the converse representation statement is covered by row T16 (the converse of Definition 2.1, commit `1af10d8`); cross-product preservation is recorded in I2.
4. Use the checked exponential, screw, bracket, adjoint, velocity, and wrench/work interfaces as prerequisites for selected kinematics; keep the remaining quaternion/rotation and reciprocal-geometry gaps explicit.
5. Extend toward a two-link FK/Jacobian connection, a workspace certificate, and an energy identity as their prerequisites become available.

This sequence exercises geometry, design, differentiation, and mechanics without committing to one application. The present increments include actual exponential existence, selected coordinates, geometric screw motion, adjoints and brackets, velocity composition, and wrench work with selected exact examples. They do not complete P1/P2. Later increments added joint and chain models, kinematics, dynamics, controllers, grasping and constrained dynamics (see [Current state](#current-state)); numerical refinement beyond the planar arm demo remains future work.

## Evidence and review

- Inspect the actual theorem and definitions against the intended claim.
- Record source references and every changed/added/omitted assumption.
- Compile affected modules and inspect the result.
- Audit dependencies for placeholder proofs and custom trust assumptions. Standard foundational axioms differ from assuming a robotics theorem.
- Include meaningful concrete instances when they check conventions or show satisfiable hypotheses; avoid tests that repeat definitions.
- Keep incomplete explorations visibly separate from established claims.
- Leave fidelity, usefulness, and acceptance to human judgment of the artifact and evidence. Kernel acceptance proves the formal derivation, not that the specification captures the intended physical robot.

Use **Failed**, **Verified**, and **Unverified** with precise scope. A verified statement must name the theorem/build and evidence, rather than label the whole physical model or research direction.

## Research directions kept open

| Direction | Shared foundation | Additional research beyond MLS |
|---|---|---|
| Robot design | Workspace, singularity, actuation, force transmission | Design grammar, task quantifiers, search/certification interface, tolerances |
| Compositional robotics | Frame, energy, constraint, attachment laws | Component contracts and implementation semantics |
| Control | Dynamics structure and stability arguments | Robustness bounds, sampling/actuator effects, richer controllers |
| Planning | Constraint geometry, controllability, steering | Collision models, global planning, execution error bounds |
| Learning | Mechanical structure and formal specifications | Residual bounds, invariant domains, checked candidate certificates |
| Robot software V&V | Plant models and abstraction maps | Veil/Z3 transition models, refinement, runtime evidence |

No application is the mandatory next branch. The architectural objective is reuse with clear assumptions.

## Open decisions

Frame/unit types versus propositions; concrete matrices versus global manifolds; serial/tree/constrained robot syntax; actual foundational gaps at the pinned mathlib release; numerical representation and solver trust; and measurable coverage for “most of the book.”

There is no supported calendar estimate for the full project yet. Use the first mathematical slices to estimate proof and integration costs.
