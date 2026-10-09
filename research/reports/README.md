# Research reports

Prepared 2026-10-08 for a Lean robotics library based on Murray, Li, and Sastry's *A Mathematical Introduction to Robotic Manipulation*.

## Reading order

1. [MLS-to-Lean assessment](mls-lean-assessment.md): source-backed coverage, potential payoffs, assumptions, and limits across geometry, dynamics, control, design, planning, and learning.
2. [Lean library roadmap](lean-library-roadmap.md): work packages, dependencies, evidence requirements, and the current implementation status.
3. [MLS coverage ledger](mls-coverage-ledger.md) and [geometry conventions](geometry-conventions.md): source-level obligations, formal status, and explicit coordinate choices.
4. [Veil and robotics verification](veil-robotics-verification.md): transition-system verification alongside mathematical formalization and Z3, including current trust and compatibility limits.

## Intent and status

The goal is to translate most of the book's mathematical core into a reusable baseline for multiple robotics research directions. Workspace-defined design is one example. The user's R-DTLGN work establishes prior Z3 experience; it does not limit this project's application scope.

The foundations now include proper rotations and rigid transforms, actual exponential existence, principal-angle and selected-coordinate results with explicit branch conditions, elementary and generic Euler formulas, coordinate/matrix Lie brackets, geometric screw motion and Chasles existence, derivative-based spatial/body velocities, and wrench power/work and reciprocity foundations. Quaternion coverage currently concerns multiplication and the norm-one group. The [repository README](../../README.md) links the modules; the [conventions](geometry-conventions.md) state the domains and remaining interpretation limits.

**Verified - formal checking:** the [final integrated build and audit](../../docs/implogs/gates/E007/20261009T042046818411474Z/summary.json), [independent evidence readback](../../docs/implogs/gates/E007/20261009T042046818411474Z/independent-evidence-review.json), and [source-statement review](../../docs/implogs/gates/E007/20261009T042046818411474Z/source-statement-review.md) bind the checked scope to named declarations and assumptions. The [ledger](mls-coverage-ledger.md) preserves historical evidence and distinguishes full, partial, and remaining source obligations. The remaining selected rows are R27, R28, X60, and K01–K16; X60 retains partial evidence. Counts are not independent theorems or a whole-book percentage.

Definitions remain noncomputable over exact reals; frames, physical units, and separate point/vector types are not enforced. A global selected exponential coordinate is supplied, but smoothness and uniqueness are not. Quaternion rotation/half-angle bridges, Euler inverse endpoint cases, missing common-normal existence and degenerate reciprocal-geometry cases, general serial-chain FK/Jacobian/IK interfaces, and exhaustive book coverage remain open. The work theorems do not establish energy balance, contact or actuator feasibility, calibration, numerical quadrature, or physical-model fidelity. User acceptance remains separate from proof checking.

## Sources and resumption

- Textbook: [references/MLS.pdf](../../references/MLS.pdf). Citations use printed pages; main-text PDF pages are 18 higher.
- Development commands: [repository README](../../README.md).
- External sources and exact Veil revision: linked in the individual reports.
- Session continuity: use the project-local reporting and handover process in `.codex` alongside this stable index.

The user authorized formalization in the 2026-10-08 America/New_York session after the Astra-only configuration resumed. The ledger, conventions, and rigid-transform foundations begin that work while retaining the broader research directions. Continue from the current handover and the ledger's remaining obligations.
