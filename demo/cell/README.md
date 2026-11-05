# The pick-and-place cell in MuJoCo

A physics evaluation of the assured pick-and-place cell: the library's three-link elbow arm (MLS Example 4.3, pp. 172–175) as a MuJoCo plant with non-idealities the proofs do not model, a 1 kHz computed-torque controller on the nominal model, and the supervised loop at period `h = 0.1 s` in which every decision (admit, reject, tick, finish, timeout) is the supervisor's answer on its line protocol. A randomized campaign measures every quantity the formal statements bound, next to the bound.

A checked theorem is about its model; this harness measures how a plant outside that model behaves. Nothing here is a proof, and the numbers are those of a simulator with stated parameters, not of a physical arm.

## Files

- `arm.py`: parameters (exact, as in the formal model), the nominal inertia matrix, Christoffel symbols and gravity term in the library's conventions, the tool map, the move reference (clamped quintic), capsule distances, and the MJCF of the plant.
- `scene.json`: the obstacles, cells, waypoints and constants of the certified scene (unchanged by the evaluation).
- `check_model.py`: MuJoCo's inertia matrix and bias forces of the nominal plant against the library's formulas at random configurations; the Christoffel table against finite differences.
- `check_distance.py`: MuJoCo's capsule-to-obstacle distances against an independent computation.
- `check_boxes.py`: the smallest capsule-to-obstacle distance over each certified cell inflated by the scene's inflation, sampled on a 41-point grid per joint, next to the certified clearance.
- `standin_supervisor.py`: a Python model of the supervisor's line protocol, kept only as the reference of `check_standin.py`, which replays its inputs through the executable and compares every answer. Every run of the evaluation is driven by the compiled executable `.lake/build/bin/cell-supervisor` (built by `lake build` from the repository root).
- `sim.py`: one supervised run and its per-move analysis.
- `cycle.py`: one cycle on the ideal and on the realistic plant.
- `jobs.py`: the runs (randomized campaign, stress sweeps, ablation of the disturbance, fault run) with fixed seeds, the planner, the drawn ranges, and the worker for one run.
- `campaign.py`: runs one mode at one (gain, tube radius) pair in parallel, one JSON line per move.
- `bounds.py`: every measured quantity of a group of moves against its bound, and the rule that picks the design point; `design_point.py` prints it.
- `summarize.py`, `figures.py`: the summary against the bounds and the figures at the design point (SVG and PDF).

## Plant

Nominal: link lengths `l₀ = 2/5`, `l₁ = 17/40`, `l₂ = 49/125` m; masses `3.7`, `8.393`, `4.9` kg; mass-centre offsets `r₀ = 1/5` (enters nothing), `r₁ = 17/80`, `r₂ = 3/10` m; principal moments as in `arm.py`; gravity `9.81` m/s² along `−z`; capsules of radius `0.06` m around the two link segments. MuJoCo 3.17, time step 0.25 ms, `implicitfast` integrator.

Non-idealities, each switchable: actuator limit 150 N·m per joint; Coulomb friction (MuJoCo `frictionloss`) and viscous friction per joint; rotor inertia (`armature`); encoders of `2^18` counts per revolution with velocity from first differences through a first-order 100 Hz low-pass filter; one control period (1 ms) of delay; a payload (point mass with the inertia of a 35 mm sphere) welded to the tool from the finish of a pick move to the finish of a place move, unknown to the controller. Contacts between the link capsules and the obstacles are active.

Model error of the plant, drawn per run: each link's mass and mass-centre offset multiplied by a factor from U[0.9, 1.1], each link's principal inertias by one factor from U[0.8, 1.2]; link lengths and joint axes stay exact, and the controller keeps the nominal model.

Campaign ranges, drawn per run: payload U[0, 5] kg (5 kg is the rated payload of the arm whose link data the model uses); Coulomb U[0, 10] N·m and viscous U[0, 10] N·m·s/rad per joint; rotor inertia U[0, 0.1] kg·m² per joint. These are generous representative ranges chosen for the evaluation, not identified from an arm. The stress sweeps, the ablation and the fault run use the middle of the ranges (payload 2.5 kg, Coulomb 5 N·m, viscous 5 N·m·s/rad, rotor inertia 0.05 kg·m², no model error) and vary one quantity.

Fault: one joint seizes during a move, modelled as a brake (a viscous damping of 10⁷ N·m·s/rad on that joint, integrated implicitly), so that the joint stays put; the supervisor's timeout and the protective stop that follows are what the run shows.

## Waypoints and planner

The scene's waypoints plus five the evaluation adds (`extra_waypoints` in `arm.py`, rational degrees, each checked to lie in a cell): pick slots `pick_4 = (45, 0, 30)` and `pick_5 = (75, 0, 30)`, place slots `place_4 = (−45, 0, 15)` and `place_5 = (−75, 0, 15)`, and a low crossing point `cross_low = (0, −30, 45)` in the cross cell only. A run goes home, then to `lift_pick`, then through four pick-place cycles over random slots (five of each); each crossing, in both directions, passes through `cross_low` with probability 1/2, and with probability 1/4 per cycle the planner also asks for an unlinked move straight to the place slot, which the supervisor rejects.

## Controller

Computed torque on the nominal model (no friction, no rotor inertia, no payload, no model error) with `K_p = ω² I`, `K_v = 2ω I`, tracking the clamped quintic reference of each admitted move with duration `T = 2` s. The loop takes one supervisor action per boundary (finish, timeout, tick or admit); a run starts with the rest move home to home admitted at boundary 0. The arrival test uses the measured sample at the boundary (quantized position, filtered velocity); the loop theorem assumes the exact sample, and the records report the difference. The arrival thresholds are `δ_a = δ` and `v_a = 2ωδ`.

Gain and tube radius: the campaign runs on the same seeds at the candidates `(ω, δ) = (120, 0.02)`, `(80, 0.03)`, `(80, 0.05)` and, for comparison, `(60, 0.05)`. The design point is the first of the first three on which every move finishes at `k₀ + ⌈T/h⌉`, no commanded torque saturates and `maxᵢ |(M̂⁻¹d)ᵢ| ≤ 0.8 ω²δ`; the stress sweeps, the ablation, the fault run and the figures use it.

## Measured per move

Tracking error `e = θ − r` and `z = ė + ωe` against the tube `|eᵢ| ≤ δ`, `|zᵢ| ≤ ωδ`; the lumped disturbance `d = M̂(θ)(ë + 2ωė + ω²e)`, which equals `M̂θ̈ + Ĉθ̇ + N̂ − τ*` with `τ*` the ideal computed torque at the true state, so it collects friction, rotor inertia, payload, quantization, filtering, delay, sampling and saturation; its Euclidean norm against `m₀ω²δ` with `m₀ = 9/100`; the acceleration-level quantity `maxᵢ |(M̂⁻¹d)ᵢ|` against `ω²δ`; the largest difference between measured and true state at the boundaries and the boundaries where the arrival test on the two disagrees; the minimum distance from each capsule to each obstacle against the certified clearance; the finish boundary against `k₀ + ⌈T/h⌉`; the tool error at the finish against `Lδ`; the peak commanded torque against the limit; the largest excursion of the configuration beyond the move's (uninflated) cell against the inflation; the largest torque step between control periods.

## Run

```
uv run python check_model.py
uv run python cycle.py out
uv run python check_boxes.py
uv run python check_standin.py 50 24
uv run python campaign.py campaign out 500 24 120 0.02     # likewise 80 0.03, 80 0.05, 60 0.05
uv run python design_point.py out                         # prints the design point, e.g. 120 0.02
uv run python campaign.py stress-payload out 5 24 120 0.02  # likewise stress-friction, ablation (1 run), fault (1 run)
uv run python summarize.py out
uv run python figures.py out
```
