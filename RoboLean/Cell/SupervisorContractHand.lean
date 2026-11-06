import RoboLean.Cell.SupervisorContract
import RoboLean.Cell.SupervisorRefines

/-!
# The supervisor's contract, proved by hand

This file proves the supervisor's contract `RoboLean.Cell.Supervisor.Contract p` for every
parameter value `p` by the hand-written route of `RoboLean.Cell.SupervisorRefines`: every state
that the executable supervisor reaches is the image of a reachable state of the design relation
`RoboLean.Design.CellSupervisor` (`reachableState_of_run`), and the invariants proved by hand for
that relation give the six clauses.

The Veil project proves the same proposition from the verification conditions of its Veil model of
the supervisor, which Veil's SMT solver discharges with proof reconstruction. The hand-written
proof here exists so that the earlier assured cell theorem, whose supervisor facts came from the
design relation, follows from the theorem that takes the contract as a premise, inside this
library.

A design statement, not from MLS. Waypoints are rational degrees; the age counts ticks.
-/

namespace RoboLean.Cell.Supervisor

/-- **The supervisor's contract, by the hand route.** For every parameter value `p`, every state
that the executable supervisor reaches from `State.init p.home` meets the six clauses of
`Contract p`, from `reachableState_of_run` and the invariants of the design relation
`RoboLean.Design.CellSupervisor`. A design statement, not from MLS; waypoints are rational degrees
and the age counts ticks. -/
theorem contract_of_design (p : Params) : Contract p := by
  intro acts s h
  refine ⟨fun hb => ?_, fun hi u hu => ?_, age_le_bound_of_run h, age_eq_zero_of_run h,
    busy_eq_false_of_run h, linked_of_run h⟩
  · obtain ⟨w, hw, hl⟩ := exists_commanded_of_run h hb
    exact ⟨w, hl, hw⟩
  · rw [commanded_eq_nil_of_run h hi] at hu
    exact List.not_mem_nil hu

end RoboLean.Cell.Supervisor
