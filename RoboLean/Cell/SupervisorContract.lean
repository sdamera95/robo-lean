import RoboLean.Cell.Supervisor

/-!
# The contract of the executable cell supervisor

This file states, as one proposition `RoboLean.Cell.Supervisor.Contract p`, what every run of the
executable cell supervisor `RoboLean.Cell.Supervisor` guarantees about the state it reaches: six
clauses on the commanded waypoint, the age and the fault flag. It proves nothing. The statement is
written with fully qualified names and imports only `RoboLean.Cell.Supervisor`, which needs no
Mathlib, so that the same text elaborates in the Veil project, which shares this library's Lean release. There,
the proposition is proved for every parameter value from the verification conditions of the Veil
model of the supervisor, which Veil's SMT solver discharges with proof reconstruction, through a
refinement from this program to that model.

The assured cell theorem of `RoboLean.Cell.AssuredContract` takes `Contract` at the cell's
parameters as a premise and draws from it the facts about the supervisor's decisions that the
motion argument needs.

A design statement, not from MLS. Waypoints are rational degrees; the age counts ticks.
-/

namespace RoboLean.Cell.Supervisor

/-- **The supervisor's contract.** For the parameters `p`, every state `s` that the executable
supervisor reaches from its initial state at `p.home` by a list of actions `acts`, each accepted,
satisfies six clauses: a busy supervisor has exactly one commanded waypoint, linked by the link
test to the waypoint the arm is at; an idle supervisor has no commanded waypoint; the age is at
most the bound; an idle supervisor has age zero; a faulted supervisor is idle; every commanded
waypoint is linked to the waypoint the arm is at. A design statement, not from MLS; waypoints are
rational degrees and the age counts ticks. -/
def Contract (p : RoboLean.Cell.Supervisor.Params) : Prop :=
  ∀ (acts : List RoboLean.Cell.Supervisor.Action) (s : RoboLean.Cell.Supervisor.State),
    RoboLean.Cell.Supervisor.run p (RoboLean.Cell.Supervisor.State.init p.home) acts = some s →
    (s.busy = true → ∃ w, RoboLean.Cell.Supervisor.linked p.cells s.current w = true ∧
        ∀ u, u ∈ s.commanded ↔ u = w) ∧
      (s.busy = false → ∀ u, u ∉ s.commanded) ∧
      s.age ≤ p.bound ∧
      (s.busy = false → s.age = 0) ∧
      (s.faulted = true → s.busy = false) ∧
      (∀ u, u ∈ s.commanded → RoboLean.Cell.Supervisor.linked p.cells s.current u = true)

end RoboLean.Cell.Supervisor
