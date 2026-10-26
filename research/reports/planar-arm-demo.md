# Planar arm demo: an executable supervisor with a checked refinement

Status, commit `b254787`: the executable supervisor, its refinement proofs and the simulation loop below are in the repository. **Verified - formal checking:** the theorems named in the evidence map are checked by Lean's kernel with only `propext`, `Classical.choice` and `Quot.sound`; they concern the formal statements. The compiler and interpreter that run the supervisor, the text protocol, the floating-point simulation and the Python harness are unverified. Nothing here concerns a physical robot.

## What the demo shows

A planar two-link arm (MLS Figure 4.4, printed p. 164) receives target points from a planner. A supervisor admits a requested target only when it lies in the arm's reachable workspace and no command is active, rejects unreachable targets, counts clock ticks while a command is active, and times the command out at a fixed age. The arm follows each admitted target under PD control. Three pieces meet in one loop:

1. **The supervisor runs as Lean code.** `RoboLean.Demo.Supervisor` is a computable timeout supervisor over rational targets (`ℚ × ℚ`), lists, a Boolean flag and a natural-number age, with core imports only. `RoboLean.Demo.Main` wraps it in a line protocol on standard input and output.
2. **Its transitions are proved to refine the design model.** `RoboLean.Demo.SupervisorRefines` proves that the executable guard decides the annulus guard `planarGuard` exactly, that every accepted action is a step of the design relation `Design.PlanarArmTimeoutSupervisor.Step` and every refused one violates a guard of that relation, and that every state reached from the initial state is a reachable design state. The design invariants therefore hold on the executable's states: the age never exceeds the bound, an idle supervisor has age zero, and every commanded target is a position of the ideal arm, reached by the elbow-down inverse kinematics (3.16) of MLS p. 98. The same supervisor is modelled in Veil, where its invariants and a bounded exclusion are checked with SMT reconstruction (see the [Veil report](veil-robotics-verification.md)).
3. **A Python loop simulates the arm and asks the supervisor.** `demo/planar_arm_demo.py` integrates the dynamics (4.10)–(4.11) of MLS pp. 164–165 under the PD law with `K_p = K_v = I`, the gains of the library's stability theorem for this arm, sends every request, admission, rejection, tick, finish and timeout to the Lean executable, and computes each set point from the inverse kinematics in floating point. It writes plots of the end-effector path, the joint angles and the supervisor timeline, and a JSON run log.

The kinematic arm of the workspace certificate points along `+y` at the zero configuration and the dynamic arm along `+x`, as in the book. `RoboLean.Demo.PlanarArmFrames` proves that for every joint vector the two tool positions agree up to the rotation `R_z(π/2)`, so the joint vector that the certificate provides for a target is a set point of the controller for the same target.

## How to run it

Build the library (`lake build`), then from `demo/`:

```sh
uv sync
uv run python planar_arm_demo.py
