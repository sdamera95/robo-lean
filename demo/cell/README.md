# The pick-and-place cell in MuJoCo

A physics evaluation of the assured pick-and-place cell: the library's three-link elbow arm (MLS Example 4.3, pp. 172–175) as a MuJoCo plant with non-idealities the proofs do not model, a 1 kHz computed-torque controller on the nominal model, and the supervised loop at period `h = 0.1 s` in which every decision (admit, reject, tick, finish, timeout) is the supervisor's answer on its line protocol. A randomized campaign measures every quantity the formal statements bound, next to the bound.

A checked theorem is about its model; this harness measures how a plant outside that model behaves. Nothing here is a proof, and the numbers are those of a simulator with stated parameters, not of a physical arm.

## Files

- `arm.py`: parameters (exact, as in the formal model), the nominal inertia matrix, Christoffel symbols and gravity term in the library's conventions, the tool map, the move reference (clamped quintic), capsule distances, and the MJCF of the plant.
- `scene.json`: the obstacles, cells, waypoints and constants of the certified scene.
- `check_model.py`: MuJoCo's inertia matrix and bias forces of the nominal plant against the library's formulas at random configurations; the Christoffel table against finite differences.
- `check_distance.py`: MuJoCo's capsule-to-obstacle distances against an independent computation.
- `standin_supervisor.py`: a Python model of the supervisor's line protocol, kept only as the reference of `check_standin.py`, which replays its inputs through the executable and compares every answer. Every run of the evaluation is driven by the compiled executable `.lake/build/bin/cell-supervisor` (built by `lake build` from the repository root).
- `sim.py`: one supervised run and its per-move analysis.
- `cycle.py`: one cycle on the ideal and on the realistic plant.
- `jobs.py`: the runs (randomized campaign, gain variants, stress sweeps, ablation of the disturbance, fault run) with fixed seeds, and the worker for one run.
- `campaign.py`: runs one mode in parallel, one JSON line per move.
- `summarize.py`, `figures.py`: the summary against the bounds and the figures (SVG and PDF).

## Plant

Nominal: link lengths `l₀ = 2/5`, `l₁ = 17/40`, `l₂ = 49/125` m; masses `3.7`, `8.393`, `4.9` kg; mass-centre offsets `r₀ = 1/5` (enters nothing), `r₁ = 17/80`, `r₂ = 3/10` m; principal moments as in `arm.py`; gravity `9.81` m/s² along `−z`; capsules of radius `0.06` m around the two link segments. MuJoCo 3.17, time step 0.25 ms, `implicitfast` integrator.

Non-idealities, each switchable: actuator limit 150 N·m per joint; Coulomb friction (MuJoCo `frictionloss`) and viscous friction per joint; rotor inertia (`armature`); encoders of `2^18` counts per revolution with velocity from first differences through a first-order 100 Hz low-pass filter; one control period (1 ms) of delay; a payload (point mass with the inertia of a 35 mm sphere) welded to the tool from the finish of a pick move to the finish of a place move, unknown to the controller. Contacts between the link capsules and the obstacles are active.

Campaign ranges, drawn per run: payload U[0, 2] kg; Coulomb U[0, 3] N·m and viscous U[0, 2] N·m·s/rad per joint; rotor inertia U[0, 0.1] kg·m² per joint. These are representative values chosen for the evaluation, not identified from a real arm.

## Controller

Computed torque on the nominal model (no friction, no rotor inertia, no payload) with `K_p = ω² I`, `K_v = 2ω I`, design gain `ω = 80` rad/s (variants 40 and 60 on the same seeds), tube radius `δ = 0.05` rad, tracking the clamped quintic reference of each admitted move with duration `T = 2` s. The loop takes one supervisor action per boundary (finish, timeout, tick or admit); a run starts with the rest move home to home admitted at boundary 0. The arrival test uses the measured sample at the boundary (quantized position, filtered velocity); the loop theorem assumes the exact sample, and the records report the difference.

## Measured per move

Tracking error `e = θ − r` and `z = ė + ωe` against the tube `|eᵢ| ≤ δ`, `|zᵢ| ≤ ωδ`; the lumped disturbance `d = M̂(θ)(ë + 2ωė + ω²e)`, which equals `M̂θ̈ + Ĉθ̇ + N̂ − τ*` with `τ*` the ideal computed torque at the true state, so it collects friction, rotor inertia, payload, quantization, filtering, delay, sampling and saturation; its Euclidean norm against `m₀ω²δ` with `m₀ = 9/100`; the acceleration-level quantity `maxᵢ |(M̂⁻¹d)ᵢ|` against `ω²δ`; the largest difference between measured and true state at the boundaries and the boundaries where the arrival test on the two disagrees; the minimum distance from each capsule to each obstacle against the certified clearance; the finish boundary against `k₀ + ⌈T/h⌉`; the tool error at the finish against `Lδ`; the peak commanded torque against the limit; how far the configuration leaves the move's cell against the inflation.

## Run

```
uv run python check_model.py
uv run python cycle.py out
uv run python check_standin.py 500 24
uv run python campaign.py campaign out 500 24
uv run python summarize.py out
uv run python figures.py out
```
