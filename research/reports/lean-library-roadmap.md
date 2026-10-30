# Roadmap for a Lean library based on MLS

Date: 2026-10-08

The current status is under [Current state](#current-state) (2026-10-26); P0–P10 below remain a dependency roadmap, not blanket completion claims.

## Objective and scope

Translate most of the mathematical core of Murray, Li, and Sastry's *A Mathematical Introduction to Robotic Manipulation* into a reusable Lean library. The purpose is a baseline for several research directions: compositional modeling, robot design, control, planning, and learning. Workspace-defined design and STL monitors are examples, not the organizing limits of the project.

The initial coverage target is Chapters 2–8, relevant foundations in Appendix A, and mathematical specifications for the computational operations in Appendix B. Chapters 1 and 9 supply context rather than a substantial theorem backlog. Exercises should be selected when they establish reusable results or expose important cases; reproducing every exercise is not an agreed requirement.

The book has been surveyed and selected central arguments inspected, not exhaustively audited. The [coverage ledger](mls-coverage-ledger.md) makes selected obligations of Chapters 2–6 and Appendix A explicit; it is not yet an exhaustive inventory of the book. “Most” should eventually be measured against the expanded ledger, with omissions and changed hypotheses recorded explicitly.

Read the [research assessment](mls-lean-assessment.md) for chapter-level evidence and the [Veil assessment](veil-robotics-verification.md) for transition-system verification. Textbook page references use printed pages in MLS.pdf; main-text printed page N is PDF page N+18.

## Current state

Status 2026-10-28: the library at commit `6342e10` and the [coverage ledger](mls-coverage-ledger.md) with the rows V01–V22 selected by that commit. The toolchain is Lean 4.34.1 with Mathlib v4.34.1, pinned in `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`. **Verified - formal checking:** `lake build` of the 215 modules imported by `RoboLean.lean` succeeds, and a whole-library axiom audit of those modules reports 7107 constants, each depending on at most `propext`, `Classical.choice` and `Quot.sound`, with no `axiom` declaration and no `opaque` stand-in. The ledger counts 315 selected MLS obligations, 310 of them Verified in full (G40 an assessment row; V10 and V14 named statements, not proved; V11 and V18 partial), and twenty-eight design rows C01–C28 separately (C25 and C27 tested, not proved; C26 a Veil-side check). These are selected obligations, not independent theorem counts or a whole-book percentage, and the work packages below remain a dependency plan rather than completion claims. The [repository README](../../README.md) links every module.

- **P0, ledger and conventions:** the ledger holds selected rows for Chapters 2–6, the first part of Chapter 7 and Appendix A with their assumptions, changed hypotheses and source observations, and the [geometry conventions](geometry-conventions.md) record the coordinate and sign choices; the rest of Chapter 7 and Chapter 8 are not inventoried.
- **P1, rigid transforms:** rows R01–R11 and T01–T15 are Verified: proper rigid transforms, composition, inverses and point and vector actions, distance and cross-product preservation, and the equivalence with homogeneous matrices. The converse characterization of distance- and cross-product-preserving maps and frame-indexed types remain open.
- **P2, twists, exponentials and wrench duality:** rows R07–R28, X01–X63 and L01–L04 are Verified, including the quaternion rotation map with its double cover and the common normal of two screw axes constructed so that the reciprocal product (2.72) covers every pair of nonparallel finite screws, with parallel and infinite-pitch cases stated apart.
- **P3, manipulator kinematics:** rows K01–K41 and the design rows C01–C07 are Verified: product-of-exponentials kinematics, spatial and body Jacobians with their derivative form (3.51)–(3.55), force pullback, workspaces, Paden–Kahan Subproblems 1–3, singular configurations, the closed-chain structure equation, manipulability, the elbow manipulator with its eight solutions under regularity hypotheses, the planar inverse kinematics (3.16), the smoothness of the forward kinematics of every order, Gruebler's formula at the velocity level, parallel mechanisms of `k` chains with kinematic and actuator singularities, self-motions with Example 3.17 and the four-bar linkage's uncertainty configuration, with a workspace certificate for the planar two-link arm. The SCARA and Stanford inverse kinematics, the Stewart platform and the exercises are not inventoried.
- **P4, energy and open-chain dynamics:** rows N01–N24 are Verified: generalized inertia, the mass matrix with symmetry and definiteness under explicit hypotheses, Christoffel symbols and the skew identity, Lagrange's and the Newton–Euler equations, potential energy and gravity, the inertia tensor, passivity and the printed matrices of Examples 4.3 and 4.4. The volume-integral derivation of (4.8)–(4.9), the spatial Newton–Euler form, Exercise 6 and friction models are open.
- **P5, trajectories, stability and controllers:** rows N25–N43 are Verified: the Lyapunov definitions, Definition 4.3's bound with named constants and its arrival time, Theorems 4.4–4.7 (the converse of Theorem 4.5 with all four bounds under a hypothesis structure for a solution flow differentiable in the initial state, discharged for linear time-varying systems; Theorem 4.6 for continuous `A(t)`), computed torque, PD and augmented PD control for the manipulator and for every robot `(M, C, N)`, exponential set-point regulation under PD with compensation of `N` on bounded sets of initial errors, workspace dynamics with Lemma 4.11, workspace computed torque and the workspace PD laws including Exercise 9, and Examples 4.5–4.7. The fourth bound for merely Lipschitz fields and Theorem 4.6 for `A(t)` with jumps (Carathéodory solutions are not adopted) are open.
- **P6, grasp and contact kinematics:** rows G01–G72 are Verified (G40 an assessment row, G41 and G61 backlog notes): contact models, friction cones, grasp maps, force-closure with Propositions 5.1–5.3, internal forces, the hand Jacobian and the grasping constraint, manipulability and Table 5.4, grasp planning with Theorems 5.4–5.6 and Theorem 5.7 assessed, and rolling contact (surface charts, the Gauss frame, the geometric parameters, Lemma 5.10, the contact coordinates, Theorem 5.11, Corollary 5.11.1, Proposition 5.12 for two chart patches, the grasp kinematics with rolling (5.40)–(5.41) with hands with rolling contacts, Examples 5.6–5.7 and Exercises 13, 14, 15 (two equal axes), 16 and 17). Table 5.3, the "only if" of Theorem 5.7 at small torsion, Theorem 5.9, Exercise 19, the three-axis ellipsoid of Exercises 14–15 and the contact set of two whole bodies are open.
- **P7, constrained dynamics and composition:** rows H01–H25 and H27–H30 are Verified: Pfaffian constraints, multipliers and the Lagrange–d'Alembert equations with Examples 6.1–6.2, the substituted Lagrangian (6.15), the hand–object system (6.16)–(6.28) with Lemma 6.1, a chart of `SE(3)` with (6.23), redundant manipulators and grasps with Example 6.3, tendons with Examples 6.4–6.5, the hand torques (6.36), and the `attach` and `control` operations on robots with Lemma 6.1 for `attach` and Example 6.7 as a one-dimensional toy. (6.32)–(6.33) are a backlog note.
- **P8, nonholonomic analysis:** rows V01–V22 (commit `6342e10`): vector fields, Lie derivatives and the Lie bracket with the book's sign and its relation to the matrix commutator and the twist bracket, Proposition 7.1, distributions and the generator criterion, the Lie algebra `L(g)` and its rank, (7.9) with the necessity half of Theorem 7.2, Proposition 7.4 ("only if"), drift-free systems with piecewise constant inputs, reachable sets and small-time local controllability, Exercise 4 and the reversal step of Proposition 7.7, the filtration with Definitions 7.2–7.3 and Exercises 10–11 (11 under the module form of `Δᵢ₊₁ = Δᵢ`), and Examples 7.2/7.7, 7.4/7.9, 7.5/7.10 and 7.6/7.11 with growth vectors, degrees, the rank condition and nonholonomy. The sufficiency half of Theorem 7.2 and Theorem 7.5 are named statements, not proved (they need flows that depend differentiably on their initial state, absent from the pinned Mathlib); Proposition 7.3, the Philip Hall basis and Exercise 11 from equal ranks are open.
- **P9, nonholonomic steering:** not started.
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

The checked subset includes hat/vee and cross-product covariance; hat powers and actual Rodrigues/exponential laws; unit-axis and rigid-exponential existence including identity and half-turn cases; elementary rotations, generic Z-Y-Z inverse coordinates, and selected principal coordinates with their domain and nonuniqueness limits. Twist carriers, matrix/coordinate brackets, adjoints, derivative-based velocities, independent screw-motion agreement, Chasles existence, and wrench power/work and reciprocal-space laws extend this foundation. Actual affine axes and finite/pure-translation/stationary cases are distinguished; scalar normalization changes the full twist and norm-based magnitude uses the absolute scalar. The [ledger](mls-coverage-ledger.md) identifies the exact Chapter 2 and selected Appendix A subset. Quaternion rotation maps, Euler inverse endpoint cases, tangent/manifold interpretations of the coordinate bracket, and remaining reciprocal-geometry cases are separate work.

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

Begin with conversions, adjoints, exponentials, FK, and Jacobians already specified mathematically. Choose a small executable representation and state its relation to the exact one.

Possible routes include exact finite/rational computation, symbolic expressions, certified approximation, and independently checked external certificates. The choice is open. Continuous energy conservation does not establish an integrator's conservation, and a proof over `ℝ` does not certify external floating-point code.

## First implementation slice

The first increment established rigid-transform foundations; later increments extend rotation representations, geometric screws, velocities, brackets, and wrench/work interfaces. The ledger identifies the exact checked subset. Continue in this order:

1. Inspect the ledger's status and evidence.
2. Review the written rigid-transform statements and concrete examples against the conventions; user acceptance remains separate from the compiled proofs.
3. Address the remaining rigid-motion obligations, including the converse representation statement, before claiming all of P1; cross-product preservation is recorded in I2.
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
