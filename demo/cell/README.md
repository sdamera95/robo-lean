# The pick-and-place cell in MuJoCo

A physics evaluation of the assured pick-and-place cell: the library's three-link elbow arm (MLS Example 4.3, pp. 172–175) as a MuJoCo plant with non-idealities the proofs do not model, a 1 kHz computed-torque controller on the nominal model, and the supervised loop at period `h = 0.1 s` in which every decision (which request to forward, reject or admit, and whether to tick, finish or time out) is taken by the compiled cell program, `RoboLean/Cell/Main.lean` on the policy of `RoboLean/Cell/Policy.lean`, on its boundary protocol. A randomized campaign measures every quantity the formal statements bound, next to the bound.

A checked theorem is about its model; this harness measures how a plant outside that model behaves. Nothing here is a proof, and the numbers are those of a simulator with stated parameters, not of a physical arm.

## Files

- `arm.py`: parameters (exact, as in the formal model), the nominal inertia matrix, Christoffel symbols and gravity term in the library's conventions, the tool map, the move reference (clamped quintic), capsule distances, and the MJCF of the plant.
- `scene.json`: the obstacles, cells, waypoints and constants of the certified scene (unchanged by the evaluation).
- `check_model.py`: MuJoCo's inertia matrix and bias forces of the nominal plant against the library's formulas at random configurations; the Christoffel table against finite differences.
- `check_distance.py`: MuJoCo's capsule-to-obstacle distances against an independent computation.
- `check_boxes.py`: the smallest capsule-to-obstacle distance over each certified cell inflated by the scene's inflation, sampled on a 41-point grid per joint, next to the certified clearance.
- `standin_supervisor.py`: a Python model of the program's line protocol (the supervisor's per-action commands and the policy's boundary protocol), kept only as the reference of `check_standin.py`, which drives runs with it, replays every line through the program and compares every answer. Every run of the evaluation is driven by the compiled program `.lake/build/bin/cell-supervisor` (built by `lake build` from the repository root); the environment variable `CELL_SUPERVISOR_CMD` replaces that command (run from the repository root), for example by `lean --run RoboLean/Cell/Main.lean` with the library on the Lean path.
- `sim.py`: one supervised run and its per-move analysis, the arrival tolerances (`tolerances`) and the realistic plant of one cycle.
- `cycle.py`: one cycle on the ideal and on the realistic plant.
- `smoke.py`: one or two cycles on the realistic plant at `(ω, δ) = (80, 0.03)`, with the per-move lines and the transcript of the protocol.
- `jobs.py`: the runs (randomized campaign, stress sweeps, ablation of the disturbance, fault run, and the sweeps of the further non-idealities: `plant` and `plant-worst` over a provisional grid, `plant-cited` and `plant-cited-worst` at values for a joint of this size from published sources, with the rotor inertia 1.7 kg·m²) with fixed seeds, the planner, the drawn ranges, and the worker for one run.
- `plant_check.py`: the elastic joints, the actuator lag, the encoder noise and the timing jitter, each on one run, against quantities recomputed from the trace (the link and rotor equations, a first-order filter of the commanded torque, the jitter and the noise drawn).
- `plant_sweep.py`: one run per setting of the further non-idealities, in parallel, with a summary line per run.
- `campaign.py`: runs one mode at one (gain, tube radius) pair in parallel, one JSON line per move.
- `bounds.py`: every measured quantity of a group of moves against its bound, and the rule that picks the design point; `design_point.py` prints it.
- `summarize.py`, `figures.py`: the summary against the bounds and the figures at the design point (SVG and PDF).

## Plant

Nominal: link lengths `l₀ = 2/5`, `l₁ = 17/40`, `l₂ = 49/125` m; masses `3.7`, `8.393`, `4.9` kg; mass-centre offsets `r₀ = 1/5` (enters nothing), `r₁ = 17/80`, `r₂ = 3/10` m; principal moments as in `arm.py`; gravity `9.81` m/s² along `−z`; capsules of radius `0.06` m around the two link segments. MuJoCo 3.17, time step 0.25 ms, `implicitfast` integrator.

Non-idealities, each switchable: actuator limit 150 N·m per joint; Coulomb friction (MuJoCo `frictionloss`) and viscous friction per joint; rotor inertia (`armature`); encoders of `2^18` counts per revolution with velocity from first differences through a first-order 100 Hz low-pass filter; one control period (1 ms) of delay; a payload (point mass with the inertia of a 35 mm sphere) welded to the tool from the finish of a pick move to the finish of a place move, unknown to the controller. Contacts between the link capsules and the obstacles are active.

Model error of the plant, drawn per run: each link's mass and mass-centre offset multiplied by a factor from U[0.9, 1.1], each link's principal inertias by one factor from U[0.8, 1.2]; link lengths and joint axes stay exact, and the controller keeps the nominal model.

Campaign ranges, drawn per run: payload U[0, 5] kg (5 kg is the rated payload of the arm whose link data the model uses); Coulomb U[0, 10] N·m and viscous U[0, 10] N·m·s/rad per joint; rotor inertia U[0, 0.1] kg·m² per joint. These are generous representative ranges chosen for the evaluation, not identified from an arm. The stress sweeps, the ablation and the fault run use the middle of the ranges (payload 2.5 kg, Coulomb 5 N·m, viscous 5 N·m·s/rad, rotor inertia 0.05 kg·m², no model error) and vary one quantity.

Further non-idealities, each off by default (the plant and every run above are then unchanged):

- Elastic joints (`stiffness`, N·m/rad per joint, `None` or 0 for the rigid plant; `joint_damping`, N·m·s/rad per joint): the two-inertia model of Spong (1987). Each joint has a motor angle `θ_m` besides the link angle `θ`; the link receives the spring torque `K (θ_m − θ) + D (θ̇_m − θ̇)` and the rotor its negative plus the actuator torque, `J θ̈_m = τ − K (θ_m − θ) − D (θ̇_m − θ̇) − friction`. The rotor inertia `J` is the `armature` of the rigid plant, and the Coulomb and viscous friction act on the rotor, on the motor side of the spring (a modelling choice: in a geared drive the motor, its bearings and the gear's input stage sit before the compliance); the links then carry neither. The rotor's kinetic energy is that of its own rotation only (Spong's simplifying assumption): in MuJoCo each rotor is a body hinged to the world, coupled to its link by a fixed tendon of length `θ_m − θ` with that stiffness and damping. A run starts at rest in static equilibrium (each spring carrying its link's gravity torque). The sweeps give the damping as the ratio `ζ` of the rotor against the held link, `D = 2ζ√(K J)`. `sense` (`"link"` or `"motor"`) says which angle the encoders read; the records (`q`, `v`, `qacc` of the trace, the tracking error, the disturbance `d` and the sample errors) are always those of the links.
- Actuator lag (`lag`, seconds): a first-order low-pass with that time constant on the torque the drive delivers, after the one-period delay and the actuator limit, integrated exactly over each simulator step with its input held.
- Encoder noise (`enc_noise`, counts): an integer drawn uniformly from `−n, …, n` for each joint at each control period and added to the encoder count; the controller and the program read the same noisy count, and the velocity estimate inherits the noise through the filter. It requires encoders (`counts`).
- Timing jitter (`jitter`, simulator steps of 0.25 ms): each control period's torque takes effect a number of steps late drawn uniformly from `0, …, n`, the torque of the previous period held meanwhile; a delay of a whole period (4 steps) means the period's torque is never applied.

The noise and the jitter are drawn from a generator seeded by `plant_seed` (default 0).

Fault: one joint seizes during a move, modelled as a brake (a viscous damping of 10⁷ N·m·s/rad on that joint, integrated implicitly), so that the joint stays put; the program's timeout and the protective stop that follows are what the run shows.

## Waypoints and planner

The scene's waypoints plus five the evaluation adds (`extra_waypoints` in `arm.py`, rational degrees, each checked to lie in a cell): pick slots `pick_4 = (45, 0, 30)` and `pick_5 = (75, 0, 30)`, place slots `place_4 = (−45, 0, 15)` and `place_5 = (−75, 0, 15)`, and a low crossing point `cross_low = (0, −30, 45)` in the cross cell only. A run goes home, then to `lift_pick`, then through four pick-place cycles over random slots (five of each); each crossing, in both directions, passes through `cross_low` with probability 1/2, and with probability 1/4 per cycle the planner also asks for an unlinked move straight to the place slot, which the program rejects.

## Controller

Computed torque on the nominal model (no friction, no rotor inertia, no payload, no model error) with `K_p = ω² I`, `K_v = 2ω I`, tracking the clamped quintic reference of each admitted move with duration `T = 2` s, from the waypoint the arm is at to the admitted goal, starting at the time of the boundary of its admission. The controller reads the measured state (quantized position, filtered velocity) at 1 kHz. On a timeout it holds the measured configuration (protective stop).

## Protocol: every decision is the program's

The harness takes no decision of the loop. It starts the program, sends `params bound h0 h1 h2 [lo0 lo1 lo2 hi0 hi1 hi2]...` (the age bound 25, the home waypoint and the cells, in degrees) and then `policy h T posTol velTol cpr`: the period and the move duration in seconds, the arrival tolerances (degrees, rad/s) and the encoder resolution in counts per revolution, each an exact rational. At every period boundary `k = 0, 1, 2, …` it sends

```
boundary k c0 c1 c2 v0 v1 v2 [a b c]...
```

with the sample, the three encoder counts `round(θᵢ / (2π / cpr))` and the three velocity estimates in rad/s, each the exact rational value `n` or `n/d` of the floating-point estimate, followed by the planner's requests that arrived since the last boundary, three angles in degrees each (the whole plan, home first, at boundary 0, and none afterwards). The program answers `ok acts=<actions> <state>`: the actions it sent to the supervisor, `request:a,b,c`, `reject:a,b,c`, `admit:a,b,c`, `finish`, `tick` or `timeout` joined by `;` (`-` when none), and its state, the supervisor's (`busy`, `faulted`, `age`, `at`, `requested`, `commanded`, `rejected`, `timedOut`) followed by the move it last admitted (`src`, `goal`, its boundary `start`) and its queue of requests (`pending`). Any other answer stops the run with an error.

The program decides, at each boundary: while a move is active, `finish` when the move is due (`start · h + T ≤ k · h`) and the sample has arrived at the goal (each joint angle `cᵢ · 360 / cpr` within `posTol` degrees of the goal's and each speed at most `velTol` rad/s), otherwise `timeout` when the age has reached the bound, otherwise `tick`; while idle and not faulted, it takes its queued requests in order, forwarding and rejecting each one not linked to the waypoint the arm is at and forwarding and admitting the first linked one; while faulted, nothing, and the queue is kept. The harness acts on the answer only: an `admit` starts the reference from `src` to `goal` at the boundary `start`; a `finish` ends the move and, at a pick or a place waypoint (the state's `at`), attaches or releases the payload; a `timeout` ends the move and starts the protective stop. The run ends one second after the program is idle with an empty queue, or faulted.

Tolerances, for the gain `ω` and the tube radius `δ`, as exact rationals: `posTol` is `δ + 1/2000` rad in degrees rounded up to a quarter degree, and `velTol = 2ωδ + 1/5` rad/s; at `(80, 0.03)` they are `7/4` degrees and `5` rad/s. The margins `1/2000` rad and `1/5` rad/s cover the difference between the sample and the true state (the encoder's half count is `π / 2^18 ≈ 1.2·10⁻⁵` rad). On the plant without quantization (`counts = 0`) the controller reads the exact position and only the sample sent to the program is quantized, at `2^40` counts per revolution.

The records keep, at every boundary, the largest difference between the sample and the true state and, while a move is due, the arrival test with the program's tolerances (in radians) on the sample and on the true state. That comparison is a record only and decides nothing.

Gain and tube radius: the campaign runs on the same seeds at the candidates `(ω, δ) = (120, 0.02)`, `(80, 0.03)`, `(80, 0.05)` and, for comparison, `(60, 0.05)`. The design point is the first of the first three on which every move finishes at `k₀ + ⌈T/h⌉`, no commanded torque saturates and `maxᵢ |(M̂⁻¹d)ᵢ| ≤ 0.8 ω²δ`; the stress sweeps, the ablation, the fault run and the figures use it.

## Measured per move

Tracking error `e = θ − r` and `z = ė + ωe` against the tube `|eᵢ| ≤ δ`, `|zᵢ| ≤ ωδ`; the lumped disturbance `d = M̂(θ)(ë + 2ωė + ω²e)`, which equals `M̂θ̈ + Ĉθ̇ + N̂ − τ*` with `τ*` the ideal computed torque at the true state, so it collects friction, rotor inertia, payload, quantization, filtering, delay, sampling and saturation; its Euclidean norm against `m₀ω²δ` with `m₀ = 9/100`; the acceleration-level quantity `maxᵢ |(M̂⁻¹d)ᵢ|` against `ω²δ`; the largest difference between the sample and the true state at the boundaries and the boundaries where the arrival test on the two disagrees (a record only); the minimum distance from each capsule to each obstacle against the certified clearance; the finish boundary against `k₀ + ⌈T/h⌉`; the tool error at the finish against `Lδ`; the peak commanded torque against the limit; the largest excursion of the configuration beyond the move's (uninflated) cell against the inflation; the largest torque step between control periods.

## Run

```
uv run python check_model.py
uv run python cycle.py out
uv run python smoke.py out 2
uv run python check_boxes.py
uv run python check_standin.py 50 24
uv run python campaign.py campaign out 500 24 120 0.02     # likewise 80 0.03, 80 0.05, 60 0.05
uv run python design_point.py out                         # prints the design point, e.g. 120 0.02
uv run python campaign.py stress-payload out 5 24 120 0.02  # likewise stress-friction, ablation (1 run), fault (1 run)
uv run python summarize.py out
uv run python figures.py out
uv run python plant_check.py
uv run python plant_sweep.py plant out 12 80 0.03
uv run python plant_sweep.py plant-worst out 12 80 0.03      # likewise 60 0.03, 40 0.03
uv run python plant_sweep.py plant-cited out 12 80 0.03
uv run python plant_sweep.py plant-cited-worst out 12 80 0.03  # likewise 60 0.03, 40 0.03
```
