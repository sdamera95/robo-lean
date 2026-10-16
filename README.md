# Robo Lean

Robo Lean is a Lean 4 library with pinned Mathlib, starting from the mathematical core of Murray, Li, and Sastry's *A Mathematical Introduction to Robotic Manipulation*. The [roadmap](research/reports/lean-library-roadmap.md), [coverage ledger](research/reports/mls-coverage-ledger.md), and [geometry conventions](research/reports/geometry-conventions.md) define the scope and assumptions.

## Library contents

### Rigid transforms and the rotation exponential

The library provides proper rotations and rigid-transform group/action laws in [RigidTransform](RoboLean/Geometry/RigidTransform.lean), a [homogeneous-matrix equivalence](RoboLean/Geometry/Homogeneous.lean), [cross-product preservation](RoboLean/Geometry/CrossProduct.lean), and [hat/vee maps](RoboLean/Geometry/Hat.lean). [HatPowers](RoboLean/Geometry/HatPowers.lean) proves the Euclidean square/cube identities, [RotationExp](RoboLean/Geometry/RotationExp.lean) packages the actual matrix exponential in `SO(3)` and proves its fixed-axis trajectory equation, and [Rodrigues](RoboLean/Geometry/Rodrigues.lean) gives unit, nonzero, and zero-axis formulas. [Rigid-transform examples](RoboLean/Examples/RigidTransform.lean) and [exponential examples](RoboLean/Examples/RotationExp.lean) state exact convention checks. [Smoke](RoboLean/Smoke.lean) remains the algebra setup check.

### Rotation representations

[RotationSurjectivity](RoboLean/Geometry/RotationSurjectivity.lean) proves unit-axis exponential representations for every proper rotation, including identity and half-turns. [RotationLog](RoboLean/Geometry/RotationLog.lean), [RotationParameters](RoboLean/Geometry/RotationParameters.lean), and [RotationAxisUniqueness](RoboLean/Geometry/RotationAxisUniqueness.lean) state principal-angle formulas, periodicity, and the exact uniqueness limits. [ElementaryRotations](RoboLean/Geometry/ElementaryRotations.lean) identifies the displayed axis-rotation matrices with actual exponentials; [EulerAngles](RoboLean/Geometry/EulerAngles.lean) proves forward Z-Y-Z formulas and a generic inverse requiring a positive radial term. [UnitQuaternion](RoboLean/Geometry/UnitQuaternion.lean) covers quaternion multiplication and the norm-one group.

### Twists and exponential coordinates

The twist foundation identifies ordered `(v, ω)` coordinates with an independent `se(3)` matrix carrier in [Twist](RoboLean/Geometry/Twist.lean). [TwistExp](RoboLean/Geometry/TwistExp.lean) uses the actual matrix exponential; [TwistExpClosedForm](RoboLean/Geometry/TwistExpClosedForm.lean) covers unit, nonunit, and zero-angular cases, and [TwistExpJacobian](RoboLean/Geometry/TwistExpJacobian.lean) proves the unit-axis translation coefficient invertible for `0 < θ < 2π`. [TwistSurjectivity](RoboLean/Geometry/TwistSurjectivity.lean) proves every rigid transform is attained, while [TwistLog](RoboLean/Geometry/TwistLog.lean) selects a noncomputable principal exponential coordinate that reconstructs the transform.

### Adjoints, brackets, and velocities

[TwistAdjoint](RoboLean/Geometry/TwistAdjoint.lean) and [TwistExpAdjoint](RoboLean/Geometry/TwistExpAdjoint.lean) connect coordinate adjoints, matrix conjugation, and actual exponentials. [TwistBracket](RoboLean/Geometry/TwistBracket.lean) and [AdjointBracket](RoboLean/Geometry/AdjointBracket.lean) connect the coordinate Lie bracket to matrix commutators and adjoint transformation. The trajectory and velocity modules derive point, spatial/body, product, and inverse laws from actual derivative hypotheses.

### Screws

[TwistScrew](RoboLean/Geometry/TwistScrew.lean), [ScrewAxis](RoboLean/Geometry/ScrewAxis.lean), and [NormalizedTwist](RoboLean/Geometry/NormalizedTwist.lean) make finite pitch, affine axes, full-twist normalization, pure translation, and stationary cases explicit. [TwistScrewMotion](RoboLean/Geometry/TwistScrewMotion.lean) identifies independently defined geometric motion with the actual exponential and proves the fixed-line mechanism formulas. [Chasles](RoboLean/Geometry/Chasles.lean) gives geometric screw-displacement existence; [ScrewConjugation](RoboLean/Geometry/ScrewConjugation.lean) proves frame-change and signed-axis conventions for that motion.

### Wrenches and reciprocity

[Wrench](RoboLean/Geometry/Wrench.lean), [WrenchScrew](RoboLean/Geometry/WrenchScrew.lean), and [Reciprocal](RoboLean/Geometry/Reciprocal.lean) cover force/torque transformations, power duality, wrench-screw parameters, and reciprocal coordinate spaces. [WrenchWork](RoboLean/Geometry/WrenchWork.lean) proves actual interval-work identities with derivative and integrability hypotheses. [WrenchReciprocityGeometry](RoboLean/Geometry/WrenchReciprocityGeometry.lean) adds geometric screw models and a common-normal formula with explicit domain and angle assumptions. Exact examples include parameterized planar mechanisms.

### Manipulator kinematics

[SerialChain](RoboLean/Kinematics/SerialChain.lean) defines serial chains and product-of-exponentials forward kinematics (MLS Chapter 3); [Jacobian](RoboLean/Kinematics/Jacobian.lean) derives the spatial and body Jacobians from actual derivatives and [ForcePullback](RoboLean/Kinematics/ForcePullback.lean) the joint torques of an end-effector wrench. [Workspace](RoboLean/Kinematics/Workspace.lean), [PadenKahan](RoboLean/Kinematics/PadenKahan.lean) (Subproblems 1–3), [Singularity](RoboLean/Kinematics/Singularity.lean), [ClosedChain](RoboLean/Kinematics/ClosedChain.lean) and [Manipulability](RoboLean/Kinematics/Manipulability.lean) cover workspaces with explicit quantifiers, inverse-kinematics subproblems with their branch conditions, singular configurations, the closed-chain structure equation and manipulability measures. The planar two-link arm (forward and inverse kinematics, workspace, singularities) and the elbow manipulator are worked out under [Examples](RoboLean/Examples).

### Open-chain dynamics

[RigidBodyInertia](RoboLean/Dynamics/RigidBodyInertia.lean), [InertiaTensor](RoboLean/Dynamics/InertiaTensor.lean), [MassMatrix](RoboLean/Dynamics/MassMatrix.lean) and [MassMatrixDerivative](RoboLean/Dynamics/MassMatrixDerivative.lean) build the manipulator inertia matrix of MLS Chapter 4 from link inertias and link Jacobians, with its differentiability and frame freedom. [Christoffel](RoboLean/Dynamics/Christoffel.lean) proves the skew symmetry of `Ṁ − 2C` for the Christoffel Coriolis matrix, [Lagrangian](RoboLean/Dynamics/Lagrangian.lean) gives Lagrange's equations and the equations of motion, [NewtonEuler](RoboLean/Dynamics/NewtonEuler.lean) the rigid-body Newton–Euler equations and [PotentialEnergy](RoboLean/Dynamics/PotentialEnergy.lean) the gravity term. For the planar two-link arm of Figure 4.4 and Examples 4.3 (three-link arm) and 4.4 (SCARA), the matrices computed from the general construction are compared with the printed ones under [Examples](RoboLean/Examples).

### Stability and control

[Stability](RoboLean/Control/Stability.lean) and [StabilityTheorems](RoboLean/Control/StabilityTheorems.lean) state the Lyapunov notions of MLS Chapter 4 §4 and Theorems 4.4 and 4.5 (sufficiency); [SolutionFlow](RoboLean/Control/SolutionFlow.lean), [LyapunovFlow](RoboLean/Control/LyapunovFlow.lean) and [GlobalFlow](RoboLean/Control/GlobalFlow.lean) supply solution flows, [LaSalle](RoboLean/Control/LaSalle.lean) proves Lasalle's principle (Theorem 4.7), and [ConverseLyapunov](RoboLean/Control/ConverseLyapunov.lean) the converse of Theorem 4.5 with three bounds for autonomous Lipschitz fields. [Linearization](RoboLean/Control/Linearization.lean) and [LinearizationTimeVarying](RoboLean/Control/LinearizationTimeVarying.lean), with [StateTransition](RoboLean/Control/StateTransition.lean) and [LinearTimeVarying](RoboLean/Control/LinearTimeVarying.lean), prove Theorem 4.6 for constant and time-varying linearizations. The manipulator controllers of §5 are in [ComputedTorque](RoboLean/Control/ComputedTorque.lean) (Proposition 4.8), [PDControl](RoboLean/Control/PDControl.lean) and [PDAsymptotic](RoboLean/Control/PDAsymptotic.lean) (Proposition 4.9, with compensation of the gravity term), [AugmentedPD](RoboLean/Control/AugmentedPD.lean) (Proposition 4.10) and [WorkspaceControl](RoboLean/Control/WorkspaceControl.lean) (workspace dynamics, Lemma 4.11 and workspace computed torque); [RobotSystem](RoboLean/Control/RobotSystem.lean) proves Proposition 4.8 once for every robot `(M, C, N)` of Chapter 6 §5.

### Grasping

[Contact](RoboLean/Grasp/Contact.lean), [FrictionCone](RoboLean/Grasp/FrictionCone.lean), [GraspMap](RoboLean/Grasp/GraspMap.lean), [ForceClosure](RoboLean/Grasp/ForceClosure.lean) and [SpatialGrasp](RoboLean/Grasp/SpatialGrasp.lean) cover the contact models, friction cones, grasp maps, force-closure (Propositions 5.1–5.3) and internal forces of MLS Chapter 5. [HandJacobian](RoboLean/Grasp/HandJacobian.lean) and [Manipulability](RoboLean/Grasp/Manipulability.lean) give the hand Jacobian, the grasping constraint and the relations of Table 5.4; [Frictionless](RoboLean/Grasp/Frictionless.lean), [PositiveSpanBounds](RoboLean/Grasp/PositiveSpanBounds.lean), [Steinitz](RoboLean/Grasp/Steinitz.lean), [ExceptionalSurface](RoboLean/Grasp/ExceptionalSurface.lean), [AntipodalGrasp](RoboLean/Grasp/AntipodalGrasp.lean) and [SpatialAntipodal](RoboLean/Grasp/SpatialAntipodal.lean) cover grasp planning (Theorems 5.4–5.6 and the "if" direction of Theorem 5.7). Examples 5.1–5.5 and the unnumbered SCARA example of §5.3 are under [Examples](RoboLean/Examples).

### Constrained and hand dynamics

[ConstrainedLagrangian](RoboLean/Dynamics/ConstrainedLagrangian.lean) formalizes Pfaffian constraints, Lagrange multipliers and the Lagrange–d'Alembert equations of MLS Chapter 6, and [SubstitutedLagrangian](RoboLean/Dynamics/SubstitutedLagrangian.lean) eq. (6.15). [CompositeDynamics](RoboLean/Dynamics/CompositeDynamics.lean), [StackedFingers](RoboLean/Dynamics/StackedFingers.lean), [ObjectChart](RoboLean/Dynamics/ObjectChart.lean) and [GraspChart](RoboLean/Dynamics/GraspChart.lean) give the hand–object system (6.16)–(6.26) with Lemma 6.1 and the link from the grasping constraint (5.15) to (6.18). [RedundantDynamics](RoboLean/Dynamics/RedundantDynamics.lean) with [PseudoInverse](RoboLean/Dynamics/PseudoInverse.lean), [Tendons](RoboLean/Dynamics/Tendons.lean) and [HandControl](RoboLean/Dynamics/HandControl.lean) cover redundant manipulators and grasps, tendon actuation and the hand torques (6.36).

### Design certificates

The five [Design](RoboLean/Design) modules mirror, in Lean, target supervisors for the planar two-link arm that are checked with Veil in a separate evaluation project beside this repository, which uses its own Lean 4.32.0 toolchain; the guard is the workspace certificate of the planar arm. The link between the Veil models and these Lean statements is a recorded convention, not a kernel-checked import ([Veil report](research/reports/veil-robotics-verification.md)).

## Verification status

**Verified - formal checking:** for the library as of commit `0361f5d` (2026-10-14), `lake build` of the 152 modules imported by [RoboLean.lean](RoboLean.lean) succeeds, and a whole-library axiom audit reports 4826 constants, each depending on at most `propext`, `Classical.choice`, and `Quot.sound`, with no other axiom, no `axiom` declaration, and no `opaque` stand-in. The [ledger](research/reports/mls-coverage-ledger.md) counts 249 selected MLS obligations, 244 of them Verified in full; R27 and R28 are open and X60 and N33 partial. Eighteen design rows, C01–C18, are counted separately. These are selected source obligations, not independent theorem counts or a whole-book percentage. Raw check outputs are kept in the maintainers' development records outside the repository; the ledger names the commit behind each row.

## Scope and open items

The library uses noncomputable definitions over exact reals. Quaternion-to-rotation and half-angle/group-map results, Euler inverse endpoint cases, remaining reciprocal-geometry cases, and the converse characterization of rigid maps remain open. In the later chapters, the fourth bound of Theorem 4.5 and its converse for general fields, rolling contact (Chapter 5 §6), the `attach` and `control` operations of Chapter 6, and Chapters 7–8 are open; the [ledger](research/reports/mls-coverage-ledger.md) and the [roadmap](research/reports/lean-library-roadmap.md) list the details. The selected exponential coordinate is not claimed smooth or unique. Frame/unit types and distinct point/vector types are not enforced; numerical refinement, physical-model fidelity, and user acceptance remain separate.

## Building

Install [elan](https://lean-lang.org/install/), then run from this directory:

```sh
lake exe cache get
lake build
```

Do not run `lake update`: the Mathlib revision is pinned in `lakefile.toml` and the resolved dependencies are checked in as `lake-manifest.json`. A pin change is a recorded decision, not a routine step.

## Development

Open the folder in VS Code with the Lean 4 extension for interactive checking. Add future project modules under `RoboLean/` and import them from `RoboLean.lean` when they should be part of the default build. The Lean version is in `lean-toolchain`; Mathlib is pinned in `lakefile.toml` and resolved in the checked-in `lake-manifest.json`.

## License

License: [MIT](LICENSE). The textbook itself is not part of this repository; citations use its printed page numbers.
