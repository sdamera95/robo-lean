# Roadmap for a Lean library based on MLS

Date: 2026-10-08

Status updated 2026-10-09 UTC: **Verified - formal checking:** the build and axiom audit of commit `b2d79fe`, with an independent readback of its evidence, check the named rotation, twist, screw, velocity, bracket, and wrench/work foundations. The [coverage ledger](mls-coverage-ledger.md) records the actual selected obligations and their assumptions, including partial and remaining rows. These are not independent theorem counts or a whole-book percentage. P0–P10 below remain a dependency roadmap, not blanket completion claims.

## Objective and scope

Translate most of the mathematical core of Murray, Li, and Sastry's *A Mathematical Introduction to Robotic Manipulation* into a reusable Lean library. The purpose is a baseline for several research directions: compositional modeling, robot design, control, planning, and learning. Workspace-defined design and STL monitors are examples, not the organizing limits of the project.

The initial coverage target is Chapters 2–8, relevant foundations in Appendix A, and mathematical specifications for the computational operations in Appendix B. Chapters 1 and 9 supply context rather than a substantial theorem backlog. Exercises should be selected when they establish reusable results or expose important cases; reproducing every exercise is not an agreed requirement.

The book has been surveyed and selected central arguments inspected, not exhaustively audited. The [coverage ledger](mls-coverage-ledger.md) makes selected rotation, rigid-transform, twist/adjoint/wrench, and kinematic obligations explicit; it is not yet an exhaustive inventory of the book. “Most” should eventually be measured against the expanded ledger, with omissions and changed hypotheses recorded explicitly.

Read the [research assessment](mls-lean-assessment.md) for chapter-level evidence and the [Veil assessment](veil-robotics-verification.md) for transition-system verification. Textbook page references use printed pages in [MLS.pdf](../../references/MLS.pdf); main-text printed page N is PDF page N+18.

## Setup baseline and current increment

- Lean toolchain: `leanprover/lean4:v4.34.1`.
- mathlib dependency: `v4.34.1`, with resolved dependencies in `lake-manifest.json`.
- Package/library: `roboLean` / `RoboLean`, renamed from the original `rooboLean` / `RooboLean` spelling.
- Setup theorem: `RoboLean.add_sq`, in `RoboLean/Smoke.lean`, proved by `ring`.
- Original setup evidence: `lake build` compiled the algebra project; `#print axioms add_sq` reported only `propext`, `Classical.choice`, and `Quot.sound`. The renamed theorem was rechecked in the combined audit.
- The Lean 4 VS Code extension was installed; interactive editor behavior was not tested.

The original setup established only the algebra proof/build baseline. Later increments add proper rigid-transform and homogeneous-matrix laws, cross-product/hat identities, actual rotation and rigid exponential existence, explicit rotation-parameter domains, noncomputable selected exponential coordinates, coordinate brackets and adjoints, geometric screw motion, velocity laws, and wrench power/work and reciprocity. The [repository README](../../README.md) links modules and the [ledger](mls-coverage-ledger.md) preserves each increment's evidence. Exact-real definitions remain noncomputable; frame/unit types and separate point/vector types are not enforced. Remaining rotation/quaternion, reciprocal-geometry, general kinematics, and arbitrary rigid-map characterization obligations stay explicit.

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

This sequence exercises geometry, design, differentiation, and mechanics without committing to one application. The present increments include actual exponential existence, selected coordinates, geometric screw motion, adjoints and brackets, velocity composition, and wrench work with selected exact examples. They do not complete P1/P2. General joint/chain models and FK/Jacobian/IK interfaces, dynamics, controllers, and numerical refinement remain future work.

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
