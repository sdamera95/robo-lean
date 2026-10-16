# Research reports

Prepared 2026-10-08 for a Lean robotics library based on Murray, Li, and Sastry's *A Mathematical Introduction to Robotic Manipulation*.

## Reading order

1. [MLS-to-Lean assessment](mls-lean-assessment.md): source-backed coverage, potential payoffs, assumptions, and limits across geometry, dynamics, control, design, planning, and learning.
2. [Lean library roadmap](lean-library-roadmap.md): work packages, dependencies, evidence requirements, and the current implementation status.
3. [MLS coverage ledger](mls-coverage-ledger.md) and [geometry conventions](geometry-conventions.md): source-level obligations, formal status, and explicit coordinate choices.
4. [Veil and robotics verification](veil-robotics-verification.md): transition-system verification alongside mathematical formalization and Z3, including current trust and compatibility limits.

## Intent and status

The goal is to translate most of the book's mathematical core into a reusable baseline for multiple robotics research directions. Workspace-defined design is one example. Earlier Z3 work in the R-DTLGN project establishes prior experience with SMT encodings; it does not limit this project's application scope.

As of commit `0361f5d` (2026-10-14) the library has 152 modules. They cover Chapter 2 (rotations, rigid transforms, exponentials and their coordinates, twists, screws, velocities, adjoints, brackets, wrenches and reciprocity) apart from the quaternion rows R27 and R28 and part of X60; Chapter 3 (product-of-exponentials kinematics, Jacobians, force pullback, workspaces, Paden–Kahan subproblems, singularities, closed chains, manipulability); Chapter 4 (the inertia matrix, Christoffel symbols, Lagrange's and the Newton–Euler equations, Lyapunov stability with Theorems 4.4–4.7, computed torque, PD and augmented PD control, workspace dynamics); Chapter 5 §§2–5 (contact models, grasp maps, force-closure, the hand Jacobian, manipulability, grasp planning); Chapter 6 §§1–5 apart from the `attach` and `control` operations (Pfaffian constraints and multipliers, the hand–object system, redundancy, tendons, hand control); and design modules that mirror Veil supervisors for the planar two-link arm. The [repository README](../../README.md) links the modules; the [conventions](geometry-conventions.md) state the domains and remaining interpretation limits.

**Verified - formal checking:** for the library as of commit `0361f5d`, `lake build` succeeds and a whole-library axiom audit reports 4826 constants, each depending on at most `propext`, `Classical.choice`, and `Quot.sound`, with no other axiom, no `axiom` declaration, and no `opaque` stand-in. The [ledger](mls-coverage-ledger.md) counts 249 selected MLS obligations, 244 of them Verified in full; R27 and R28 are open and X60 and N33 retain partial evidence. The eighteen design rows C01–C18 are counted separately. Counts are not independent theorems or a whole-book percentage. Raw check outputs (build logs, axiom audits, instance files) are kept in the maintainers' development records outside the repository; the published evidence anchor is the commit named in each ledger row.

Definitions remain noncomputable over exact reals; frames, physical units, and separate point/vector types are not enforced. A global selected exponential coordinate is supplied, but smoothness and uniqueness are not. Quaternion rotation/half-angle bridges, Euler inverse endpoint cases, missing common-normal existence and degenerate reciprocal-geometry cases, the fourth bound of Theorem 4.5 and its converse for general fields, rolling contact (Chapter 5 §6), the `attach` and `control` operations, Chapters 7–8, and exhaustive book coverage remain open. The work theorems do not establish energy balance, contact or actuator feasibility, calibration, numerical quadrature, or physical-model fidelity. User acceptance remains separate from proof checking.

## Sources

- Textbook: [references/MLS.pdf](../../references/MLS.pdf). Citations use printed pages; main-text PDF pages are 18 higher.
- Development commands: [repository README](../../README.md).
- External sources and exact Veil revision: linked in the individual reports.

Formalization began on 2026-10-08 with the ledger, the conventions, and the rigid-transform foundations, while retaining the broader research directions. The ledger's remaining obligations and the roadmap's work packages describe what is open.
