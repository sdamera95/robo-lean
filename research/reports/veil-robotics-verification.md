# Veil for robotics verification and validation

**Research note — 2026-10-08.** This assessment concerns [Veil's `main` branch at commit `b05ef68`](https://github.com/verse-lab/veil/commit/b05ef68eb9e29cff3168d1a2a34acd314e26a59e), with [Loom `a8f7993` and Lean-SMT `922af46` pinned by its manifest](https://github.com/verse-lab/veil/blob/b05ef68eb9e29cff3168d1a2a34acd314e26a59e/lake-manifest.json). It is a source review, not an experimental evaluation: Veil was not installed or run, and no robotics guarantee has been established here.

## Assessment

Veil can be useful for robotics systems that admit a **state-transition model**, particularly supervisory control, mode and fault handling, task and behavior transitions, multi-robot coordination protocols, and runtime-monitor logic. It is less directly suited to proving continuous plant dynamics, geometric safety, learned-policy performance, or full hybrid-system reachability. Those subjects can still participate in a Lean-centered assurance program, but their mathematical models and the bridge from them to Veil's discrete transitions require separate work. This is an assessment of fit, not a claim that Veil already has robotics-specific libraries.

Veil's distinctive contribution is the integration of a transition-system language, concrete and symbolic exploration, generated invariant proof obligations, and interactive Lean proofs around a shared formal model. The [Lean use-case page](https://lean-lang.org/use-cases/veil/) describes this vision; the [current Veil documentation](https://github.com/verse-lab/veil/blob/b05ef68eb9e29cff3168d1a2a34acd314e26a59e/docs/DSL-Reference.md) supplies the operative commands and their scope. Existing Z3-based bounded model checking remains useful. Z3 can also discharge inductive proof obligations when those are encoded; Veil does not make an otherwise impossible solver argument possible. Its advantage is the shared semantics, generated obligations, trace tools, and access to Lean's proof language when automation stops.

## What is implemented

| Mechanism | Present scope | Interpretation |
| --- | --- | --- |
| `sat trace` / `unsat trace` | SMT-based symbolic exploration of a specified, bounded number of actions, over the module's abstract parameters | Finds or excludes paths of the specified shape and depth; a bounded UNSAT result proves the modeled bounded claim if that is the intended contract. |
| `#model_check` | Explicit exploration of a supplied finite type/theory instance; `maxDepth := 0` means no depth cap | Can cover every reachable state of that finite instance if the search exhausts it. A depth cap limits coverage unless the reachable state space is exhausted before the cap; other instances are not covered. |
| `#simulate` | Random walks over a concrete instance | Useful empirical model validation, without exhaustive coverage. |
| `#check_invariants` | Checks initialization and preservation of the conjunction of `safety` and `invariant` clauses under each action | A successful inductive argument establishes the state property for arbitrarily many steps of the modeled transition system, subject to the proof's trust assumptions. Counterexamples to induction guide strengthening. |
| Interactive Lean theorem | Inserts a failed verification condition as a theorem stub that can be proved with Lean tactics and registered with `@[veil]` | Provides a path when SMT automation is insufficient. |

These behaviors are described in the [DSL reference](https://github.com/verse-lab/veil/blob/b05ef68eb9e29cff3168d1a2a34acd314e26a59e/docs/DSL-Reference.md) and [model-checker guide](https://github.com/verse-lab/veil/blob/b05ef68eb9e29cff3168d1a2a34acd314e26a59e/docs/ModelChecker-Guide.md). The latter explicitly says the checker tests only the supplied instance and theory, that `state_constraint` removes states from exploration, and that its `termination` clause affects deadlock reporting but does not prove eventual termination. The [current README](https://github.com/verse-lab/veil/blob/b05ef68eb9e29cff3168d1a2a34acd314e26a59e/README.md) calls liveness a future capability and labels Veil 2.0 a pre-release with remaining rough edges. One-step invariant induction is documented; a general k-induction command is not documented in these sources.

There are two different ways a bounded result can matter. If the requirement itself is finite-horizon—such as a monitor's output for traces of length at most its specified horizon—bounded UNSAT can fully establish that modeled requirement, provided the encoding covers all intended inputs and cases. If the requirement quantifies over an unbounded execution, the same bounded result is only a finite prefix check; induction, a complete finite-state search, or another argument is needed. This distinction is logical, not specific to Veil.

## Foundations and trust boundary

Veil 2 actions are expressed using Loom's common semantics for mutable state, immutable theory, exceptions, nondeterministic choice, and possible divergence. The [Loom POPL 2026 paper, Section 7.1](https://verse-lab.org/papers/loom-popl26.pdf) explains how the verification and symbolic-transition interpretations are derived from that common representation. This is valuable for avoiding drift between separately maintained executable and proof models. It does **not** establish that a researcher chose the right robot model, that sensor and actuator interfaces satisfy its assumptions, or that generated code matches a physical deployment.

The [Lean use-case page](https://lean-lang.org/use-cases/veil/) says external solver proofs are checked by Lean's kernel. This needs a qualification for the current default: [`veil.smt.trust` defaults to `true`](https://github.com/verse-lab/veil/blob/b05ef68eb9e29cff3168d1a2a34acd314e26a59e/Veil/Base.lean), which trusts SMT UNSAT results. Setting `set_option veil.smt.trust false` makes the [Veil SMT tactic request reconstruction](https://github.com/verse-lab/veil/blob/b05ef68eb9e29cff3168d1a2a34acd314e26a59e/Veil/Frontend/DSL/Tactic.lean). Veil [warns when a successful verification witness contains `sorry`](https://github.com/verse-lab/veil/blob/b05ef68eb9e29cff3168d1a2a34acd314e26a59e/Veil/Frontend/DSL/Module/Elaborators/Verification.lean). Reconstruction is therefore available, but it is not the default and is not a promise that every query will reconstruct. For a high-assurance result, inspect the final theorem statement, assumptions, imported axioms, and proof dependencies; do not infer kernel-checked status merely from a green SMT result or a counterexample-free run.

The stock Veil tactic invokes [Lean-SMT's `smt` tactic](https://github.com/verse-lab/veil/blob/b05ef68eb9e29cff3168d1a2a34acd314e26a59e/Veil/Frontend/DSL/Tactic.lean), whose [pinned fork README](https://github.com/verse-lab/lean-smt/blob/922af463373ce3f74d7b1aee36c6391f867aaaa2/README.md) describes a cvc5 query and optional replay of cvc5's proof. This is not direct reuse of an existing Z3 Python model or solver script. Translating a Z3 model into Veil creates a specification-equivalence obligation; a cross-check on representative and adversarial traces is a sensible first validation step.

## Robotics applications and interfaces

Good initial candidates are finite or discretely sampled components whose correctness is naturally a property of event order and state: an emergency-stop and reset protocol; a mode selector with mutually exclusive modes; fault detection, latching, and recovery; an arbitration layer between planner and safety controller; a bounded-history temporal monitor; and message ordering or lease ownership among robots. A ternary monitor can use an enum for true, false, and unknown, plus counters or history state. Its safety clauses might state that unknown does not grant permission, a latched fault cannot silently clear, or an actuator command requires a valid enabling state. These are proposed models, not built-in Veil predicates or native STL syntax.

A longer-term Lean-centered architecture could put continuous mathematics, geometry, and dynamics in Lean/mathlib or other specialized libraries; prove that a discretization, robust guard, or reachable-set bound soundly abstracts the plant; use Veil or Z3 to analyze the resulting transition system; and separately test or verify the implementation-to-model mapping. The critical interface is the refinement statement: which continuous trajectories and sampled observations are represented by each abstract transition, including what can happen **between samples**. Bounds on disturbances, latency, sensor error, controller behavior, and environment actions must appear as explicit assumptions and be justified with proofs, measurements, or conservative contracts. A discrete safety result alone cannot exclude an inter-sample collision or an unmodeled actuator response.

Learned components fit when their relevant behavior can be enclosed by a justified contract: for example, an output range, classification uncertainty, or guard-enforced action set. Veil can reason about the supervisor consuming that contract. Establishing the contract for a neural policy, distribution shift, perception error, or closed-loop robustness is a separate verification and validation problem. Direct Lean proofs are often preferable for mathematical facts about control laws, geometry, estimators, and abstraction relations; Veil is most attractive after those facts have been expressed as state and transition obligations. Existing Z3 workflows remain a strong choice for rapid bounded counterexample search and may also encode induction directly.

## Practical constraints and a first evaluation

The pinned [Lean-SMT README](https://github.com/verse-lab/lean-smt/blob/922af463373ce3f74d7b1aee36c6391f867aaaa2/README.md) advertises uninterpreted functions and **linear** integer/real arithmetic with quantifiers; real arithmetic requires mathlib, while bitvectors are experimental. Veil's [locked dependencies](https://github.com/verse-lab/veil/blob/b05ef68eb9e29cff3168d1a2a34acd314e26a59e/lake-manifest.json) do not include mathlib, and the pinned fork's [build file](https://github.com/verse-lab/lean-smt/blob/922af463373ce3f74d7b1aee36c6391f867aaaa2/lakefile.lean) excludes its mathlib/Real tests. Consequently, linear real arithmetic support in the broader Lean-SMT project is not evidence that a stock Veil installation proves nonlinear robot dynamics. No native STL/MTL parser, ODE solver, or hybrid reachability workflow is evidenced by the reviewed Veil documentation.

Veil currently pins [Lean v4.32.0](https://github.com/verse-lab/veil/blob/b05ef68eb9e29cff3168d1a2a34acd314e26a59e/lean-toolchain), while this project's newly established mathlib setup uses Lean v4.34.1. An isolated Veil evaluation project at its pinned version is the lowest-friction way to assess a small discrete model before attempting dependency integration; that evaluation had **not** been performed when this report was written; it was performed on 2026-10-10 (section below). A useful first model would be one supervisory or monitor automaton, accompanied by a non-vacuity trace, an intentional unsafe trace that the checker can find, a bounded exclusion query, and a small inductive invariant with reconstruction enabled. Inspect the resulting Lean theorem and assumptions, then compare the modeled transitions with the existing implementation or Z3 encoding. This would measure the actual value of Veil for the project without assuming its protocol-oriented examples transfer automatically to robotics.

**Evidence status:** This report is a source-based assessment of current capabilities and limits. A formal robotics guarantee would require a stated model and discharged proof or model-checking obligations, with the trust boundary identified. Empirical validation would require traces, tests, or physical evidence about a particular implementation and environment. Neither has been established for the robotics system by this report.

## First evaluation, 2026-10-10 (E018)

The evaluation recommended above was run on Veil
`main` at 0263f6c (Lean 4.32.0) with a five-target supervisor for the planar two-link arm ([entry E018](../../docs/implogs/E018-veil-pilot-planar-arm-supervisor.md), [gate](../../docs/implogs/gates/E018/20261010T212023Z/)) whose
guard the Robo Lean workspace certificate makes sound. All four kinds of check ran, each file in
about 6 s: an exhaustive `#model_check` of one finite instance, `sat trace` non-vacuity queries,
a bounded `unsat trace` over six actions and `#check_invariants`; a deliberately unsafe variant
(the guard removed from `admit`) failed every check that should fail. With `veil.smt.trust
false`, proof reconstruction succeeded for the five verification conditions that reached the
solver, and `#print axioms` on the ten generated theorems shows only `propext`,
`Classical.choice` and `Quot.sound`; with trust on, the same five theorems depend on `sorryAx`.
Three qualifications follow from the run and the source. The generated theorems are
per-condition statements over Veil's encodings (`meetsSpecificationIfSuccessfulAssuming` of an
action against the assumptions and invariants); no generated theorem states that every
reachable state of the module's transition system satisfies the invariant, so that composition
rests on Veil's design and was supplied separately in Lean for the mirrored system. An `unsat
trace` result carries no proof term even with trust off (the trace discharger records a proven
result without a witness), so it is a solver verdict. The model is propositional, so the run
says nothing about reconstruction for arithmetic, for larger models or for quantifier-heavy
protocols. The link from Veil's uninterpreted guard to the continuous Lean theorem remains a
recorded convention while the two projects use different Lean versions.

## Second evaluation, 2026-10-11 (E022)

The arithmetic follow-up of the first evaluation was run
on the same Veil commit with the E018 supervisor extended by a command age: `tick` increments an
integer `age` while `age < bound`, `timeout` clears the command when `age = bound`, and the clauses
include `age ≤ bound` ([entry E022](../../docs/implogs/E022-veil-second-pilot-timeout-supervisor.md),
[gate](../../docs/implogs/gates/E022/20261011T001058Z/)). Integer state needed no special treatment in
the explicit-state checker: the reachable ages are bounded, so `#model_check` exhausted 9216 states
of a five-target instance with `bound := 3`, and the deliberately unsafe variant (the bound guard
removed from `tick`) was refuted by every check that should fail. With `veil.smt.trust false`, all
21 clause conditions reached cvc5 and were reconstructed into Lean proofs that depend only on
`propext`, `Classical.choice` and `Quot.sound`; no condition failed, timed out or needed
`veil.smt.timeout`, `veil.solver grind` or a hand proof, and the replays took 35 to 68 ms each in the final gate run. The
arithmetic exercised was small: one condition (`tick` preserves `age ≤ bound`) needed a linear
integer inference, which cvc5 proved with its arithmetic rewriting and bound-tightening rules and
lean-smt replayed through its integer polynomial normalizer; two frame conditions used arithmetic
normalization; Veil's preprocessing closed the arithmetic of the reset conditions before the
solver. The run therefore shows that reconstruction handles linear integer arithmetic of this
size, not that it scales to sums, several counters, arithmetic under quantifiers or nonlinear
terms. The bounded `unsat trace` was refuted by cvc5 with a 3705-step proof containing arithmetic
rules, but Veil keeps no Lean proof term for trace queries, so it remains a solver verdict. One
qualification of the first evaluation was removed: the per-condition theorems can be composed in
Lean, inside the Veil file, into a theorem that every reachable state of the module's assembled
transition system satisfies all clauses, with a lemma that this system has a reachable state; the
proof uses Veil's own lemmas relating its specifications to its transition relation and needs the
instance arguments written out. Veil's DSL elaboration (actions to programs, clauses to
predicates) remains part of the trusted base, and the link to the continuous Lean theorems remains
a recorded convention.

## Third evaluation, 2026-10-11 (E027)

The question left by the second evaluation, where reconstruction stops as the arithmetic gets
richer, was run on the same Veil commit with the timeout supervisor extended by three counters
([entry E027](../../docs/implogs/E027-veil-third-pilot-budget-supervisor.md),
[gate](../../docs/implogs/gates/E027/20261011T150354Z/)): a per-target admission count
`attempts : target → Nat` bounded by `maxAttempts` (arithmetic under a quantifier), the sum
invariant `ticksClosed + age = ticksTotal` (which needs the auxiliary clause that an idle supervisor
has age zero), and a tick budget decremented by `budget := budget - 1` under `require budget ≥ 1`
with the invariant `budget + ticksTotal = capacity` (truncated subtraction). With
`veil.smt.trust false`, all 41 clause conditions that reached cvc5 were reconstructed into Lean
proofs that depend only on `propext`, `Classical.choice` and `Quot.sound`, each in at most 100 ms;
no condition failed or timed out, so no knob was needed. Verdict per feature: arithmetic under a
quantifier reconstructed (cvc5 instantiates the quantified invariant and eliminates the `ite` of
the function update; lean-smt replays the instantiation by application and the arithmetic through
its integer lemmas); the sum invariant reconstructed (a Farkas-style combination of the invariant,
the auxiliary clause and the guard); truncated subtraction reconstructed (lean-smt rewrites
`budget - 1` into an `if`, cvc5 eliminates it with the guard). The deliberately unsafe variant
without the budget guard was refuted by every check, with counterexamples that need `0 - 1 = 0`, so
the solver sees the truncation. Two qualifications. First, the diagnostic `trace.smt.solve`, which
prints cvc5's proof, makes the check fail on such a model: lean-smt's encoding of a `Nat`-valued
function adds a quantifier whose bound variable `a₁` is not ASCII, and cvc5's proof printer rejects
it; the untraced check is unaffected, and `trace.smt` (goal and query) works. Second, the run says
nothing about nonlinear terms, `div`/`mod` or much larger models; the bounded `unsat trace` query's
proof grew to 27129 steps (3705 in the second evaluation), but Veil does not reconstruct trace
queries. As before, Veil's DSL elaboration is trusted, a composition of the per-condition theorems
over the reachable states was proved in Lean inside the Veil file, and the link to the continuous
Lean theorems remains a recorded convention.

## Related Z3 work in this research program

A companion source review identified a [current symbolic-unrolling path](</home/sandeep/research/projects/R-DTLGN/icra-outputs/runs/2026-09-20D-thermometer-rho-campaign/z3-code/_bmc8.py:78>), a [Bool-pair ternary encoder](</home/sandeep/research/projects/R-DTLGN/r_dtlgn/smt/encoder_bool.py:26>), and a [newer inductive-step experiment](</home/sandeep/research/projects/R-DTLGN/icra-outputs/certification/observed-envelope/_step.py:108>). Their presence shows the project already extends beyond a simple bounded-checking script; this report does not establish that the inductive experiment produced a successful unbounded certificate. One possible Lean contribution, independent of adopting Veil, is to prove the encoder agrees with a finite ternary evaluator for arbitrary circuits and ticks. Agreement between a learned policy and an STL requirement would remain a separate claim. These Z3 examples provide methodological context and do not limit Veil's possible uses across robotics, control, and learning.
