# Planar arm demo: an executable supervisor with a checked refinement

Status, commit `b254787` (the native executable target since commit `d8e99a5`): the executable supervisor, its refinement proofs and the simulation loop below are in the repository. **Verified - formal checking:** the theorems named in the evidence map are checked by Lean's kernel with only `propext`, `Classical.choice` and `Quot.sound`; they concern the formal statements. The compiler and interpreter that run the supervisor, the text protocol, the floating-point simulation and the Python harness are unverified. Nothing here concerns a physical robot.

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
```

The script starts the supervisor with `lake env lean --run RoboLean/Demo/Main.lean`, run in the top directory of the repository, or with the command in the environment variable `ROBO_LEAN_SUPERVISOR`, and writes `demo/out/`. `lake build` also compiles the supervisor to a native executable, the Lake target `planar-arm-supervisor` (`.lake/build/bin/planar-arm-supervisor`, run with `lake exe planar-arm-supervisor`); setting `ROBO_LEAN_SUPERVISOR='lake exe planar-arm-supervisor'` makes the loop use it. On the scripted protocol transcript the native executable and the interpreter give the same thirty-three answers (a test). The supervisor can also be driven by hand, through either command, with one command per line: `params a b bound` (positive rational link lengths written `n`, `n/d` or `n.f`, a natural age bound; resets the state), `request x y`, `admit x y`, `reject x y`, `finish`, `tick`, `timeout`, `state`, `quit`. Each line is answered with `ok <state>`, `blocked <guard>` or `error <reason>`.

The demo's parameters are its own choice; MLS prints none for this arm: `l₁ = 1`, `l₂ = 1/2`, homogeneous bars with `m₁ = m₂ = 1`, mass centres at mid-link, `I_zi = mᵢlᵢ²/12`, horizontal plane (no gravity term, the book's `L = T`), control period 0.5 s, age bound 18 ticks, arrival tolerance 0.02. The scripted scenario has eleven requests: seven inside the annulus `1/2 ≤ r ≤ 3/2` (one exactly on the outer circle), four outside, several arriving while a command is active, and one slow target that times out.

## Evidence map

| Claim shown | Backed by | Status and limits |
| --- | --- | --- |
| Admitted targets lie in the annulus, rejected ones outside | `RoboLean.Demo.reachable_eq_true_iff`, `RoboLean.Demo.step_isSome_iff` | Kernel-checked for the Lean definitions; that the interpreter or the compiled executable computes them is trusted. An exact rational recomputation in the harness agrees with every guard answer of the scripted run (a test) |
| Every admitted target is a position of the ideal arm | `RoboLean.Demo.exists_planarTwoLinkPosition_eq_of_run`, `exists_planarArmXY_eq_of_run`, through the design refinement and the workspace certificate (reachable workspace of MLS eq. (3.12), p. 95) | Kernel-checked; position reachability of the ideal kinematic model. Veil model `PlanarArmTimeoutSupervisor`: clause `commanded_reachable` by `#check_invariants` with SMT trust off, `#model_check` on a five-target instance, six-action bounded exclusion kernel-checked in proof-term form. Reading Veil's uninterpreted `reachable` as the annulus guard is a convention |
| The age never exceeds the bound; idle means age zero | `RoboLean.Demo.age_le_bound_of_run`, `age_eq_zero_of_run` | Kernel-checked. Veil clauses `age_bounded`, `idle_age_zero`. The age counts ticks, not seconds |
| Every executable state is a reachable design state | `RoboLean.Demo.reachableState_of_run`, `step_sound`, `run_sound` | Kernel-checked for runs from the initial state; that the protocol loop reports exactly those runs holds by its code, not by a theorem |
| The set point reaches its target | `RoboLean.Demo.planarArmXY_elbowDown_of_run`, `planarArmXY_elbowDown` (MLS eq. (3.16), p. 98), the frame bridge `planarTwoLinkPosition_eq_vec_iff_planarArmXY_eq` | Kernel-checked in exact reals; the floating-point evaluation is unverified |
| The joints converge to each set point | `Examples.planarTwoLinkArm_globallyAsymptoticallyStableAt_pdCompensatedTorque'` (MLS Proposition 4.9 as formalized, p. 193) | Kernel-checked for the ideal continuous closed loop with a fixed set point; no rate or arrival time. The numerical integration and the switching of set points are unverified |
| Which target times out and when commands finish | The demo's parameters, period, bound and tolerance | Unverified: a property of the simulation; arrival is checked only at period boundaries |
| The executable's answers reach the loop unchanged | The line protocol over a subprocess pipe | Unverified (operating system, text encoding, harness); a scripted transcript with hand-derived answers matched exactly under the interpreter and under the native executable (tests) |

## Trust boundary

Kernel-checked: the design invariants of the timeout supervisor, the refinement of the executable's transitions and runs to them, the exactness of the executable guard, the reachability of every commanded target by the ideal arm with the elbow-down joint vector, the frame bridge, and the global asymptotic stability of the PD law for the ideal continuous model. Solver-checked with SMT trust off: the Veil model's invariants and traces, two bounded exclusions also kernel-checked in proof-term form. Unverified: the Lean compiler, the interpreter and the native code generator and linker, the operating system and the subprocess protocol, the floating-point inverse kinematics and integration, the chosen parameters, the behaviour between samples, and the Python harness. A trajectory that lands within tolerance illustrates the loop; it is not evidence for any theorem.

## Open items

- A differential test of Veil's executable semantics against the Lean executable through exchanged trace files (the two projects use different Lean versions and cannot import each other), and a Veil run on the demo's own target table.
- Mirrors of the budget, scheduler and wrap-around supervisors.
- A statement relating the sampled arrival test to the continuous model (an arrival-time or rate bound), and an error bound for the floating-point inverse kinematics.
