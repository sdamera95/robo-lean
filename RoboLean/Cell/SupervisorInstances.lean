import RoboLean.Cell.SupervisorRefines

/-!
# Instances of the cell supervisor on concrete data

Concrete parameters for the executable cell supervisor: three cells of joint angles in degrees
(a pick cell, a crossing cell and a place cell, with corners at multiples of 15°), a home
waypoint in the crossing cell and the age bound 25. Each statement below is checked by
evaluation on this data and instantiates the hypotheses of the refinement and invariant theorems
of `RoboLean.Cell.SupervisorRefines` and `RoboLean.Design.CellSupervisor`, so none of them is
vacuous: a pick-lift-cross-descend-place cycle runs to its end, a waypoint outside every cell
shared with the arm's waypoint is rejected and cannot be admitted, a busy and a faulted state are
reached, and a faulted supervisor blocks every admission. These are convention checks on one data
set, not general theorems, and say nothing about the certificates of the cells. A design model,
not from MLS.
-/

namespace RoboLean.Cell.Supervisor

namespace Instances

open RoboLean.Design

/-- The pick cell: base yaw 45° to 75°, shoulder −45° to 0°, elbow 0° to 30°. Concrete data, a
design model, not from MLS. -/
def pickCell : Box := { lo := (45, -45, 0), hi := (75, 0, 30) }

/-- The crossing cell: base yaw −60° to 60°, shoulder −45° to −30°, elbow 0° to 45°. Concrete
data, a design model, not from MLS. -/
def crossCell : Box := { lo := (-60, -45, 0), hi := (60, -30, 45) }

/-- The place cell: base yaw −75° to −45°, shoulder −45° to 0°, elbow 0° to 15°. Concrete data, a
design model, not from MLS. -/
def placeCell : Box := { lo := (-75, -45, 0), hi := (-45, 0, 15) }

/-- The parameters: the three cells, the home waypoint `(0°, −40°, 30°)` and the age bound 25.
Concrete data, a design model, not from MLS. -/
def params : Params :=
  { cells := [pickCell, crossCell, placeCell], home := (0, -40, 30), bound := 25 }

/-- The waypoint above the pick slot, in the pick and the crossing cell. Concrete data.
Not from MLS. -/
def liftPick : Waypoint := (50, -35, 30)

/-- A pick slot, in the pick cell only. Concrete data. Not from MLS. -/
def pickSlot : Waypoint := (50, 0, 30)

/-- The waypoint above the place slot, in the crossing and the place cell. Concrete data.
Not from MLS. -/
def liftPlace : Waypoint := (-50, -35, 15)

/-- A place slot, in the place cell only. Concrete data. Not from MLS. -/
def placeSlot : Waypoint := (-50, 0, 15)

/-- `n` clock ticks. Not from MLS. -/
def ticks (n : Nat) : List Action := List.replicate n .tick

/-- One move: request the waypoint, admit it, twenty ticks, finish. Not from MLS. -/
def move (w : Waypoint) : List Action := [.request w, .admit w] ++ ticks 20 ++ [.finish]

/-- A pick-lift-cross-descend-place cycle from home, with a request for the pick slot from home
rejected first. Concrete data. Not from MLS. -/
def cycle : List Action :=
  [.request pickSlot, .reject pickSlot] ++ move liftPick ++ move pickSlot ++ move liftPick ++
    move liftPlace ++ move placeSlot

/-- The cycle followed by a move to the lift waypoint above the place slot that is not finished:
twenty-five ticks and a timeout. Concrete data. Not from MLS. -/
def faultRun : List Action :=
  cycle ++ [.request liftPlace, .admit liftPlace] ++ ticks 25 ++ [.timeout]

/-- The state at the end of the cycle. Not from MLS. -/
def cycleState : State := (run params (State.init params.home) cycle).getD (State.init params.home)

/-- The state at the end of the fault run. Not from MLS. -/
def faultState : State :=
  (run params (State.init params.home) faultRun).getD (State.init params.home)

/-- The state in the middle of the second move, busy towards the pick slot. Not from MLS. -/
def busyState : State :=
  (run params (State.init params.home) ([.request pickSlot, .reject pickSlot] ++ move liftPick ++
    [.request pickSlot, .admit pickSlot, .tick])).getD (State.init params.home)

/-- The cycle is accepted action by action and ends idle at the place slot. Convention check by
evaluation. Not from MLS. -/
theorem run_cycle : run params (State.init params.home) cycle = some cycleState := by
  decide +kernel

/-- The cycle ends at the place slot, idle, not faulted, with the pick slot rejected. Convention
check by evaluation. Not from MLS. -/
theorem cycleState_spec :
    cycleState.current = placeSlot ∧ cycleState.busy = false ∧ cycleState.faulted = false ∧
      cycleState.rejected = [pickSlot] := by
  decide +kernel

/-- The busy state is reached, busy towards the pick slot from the lift waypoint. Convention check
by evaluation. Not from MLS. -/
theorem busyState_spec :
    run params (State.init params.home) ([.request pickSlot, .reject pickSlot] ++ move liftPick ++
      [.request pickSlot, .admit pickSlot, .tick]) = some busyState ∧
    busyState.busy = true ∧ busyState.commanded = [pickSlot] ∧ busyState.current = liftPick ∧
      busyState.age = 1 := by
  decide +kernel

/-- The fault run is accepted and ends faulted, idle, with the lift waypoint timed out and the arm
still at the place slot. Convention check by evaluation. Not from MLS. -/
theorem run_faultRun :
    run params (State.init params.home) faultRun = some faultState ∧ faultState.faulted = true ∧
      faultState.busy = false ∧ faultState.timedOut = [liftPlace] ∧
      faultState.current = placeSlot := by
  decide +kernel

/-- From home the pick slot is not linked: no cell contains both, so a request for it is rejected
and its admission is blocked. Convention check by evaluation. Not from MLS. -/
theorem pickSlot_not_linked_home : linked params.cells params.home pickSlot = false := by
  decide +kernel

/-- A faulted supervisor blocks the admission of a requested waypoint linked to the arm's
waypoint, naming the guard `faulted`. Convention check by evaluation. Not from MLS. -/
theorem faulted_blocks_admit :
    (Action.admit liftPlace).blocker params
      { faultState with requested := [liftPlace] } = some "faulted" ∧
    linked params.cells faultState.current liftPlace = true := by
  decide +kernel

/-- The refinement theorem on the cycle: its final state abstracts to a reachable state of the
design supervisor with the link relation of the three cells. Instance of
`reachableState_of_run`. Not from MLS. -/
theorem cycleState_reachable :
    CellSupervisor.ReachableState (CellLinked params.cells) params.bound params.home
      cycleState.abstract :=
  reachableState_of_run run_cycle

/-- The busy invariant on a busy reachable state: the command list is the pick slot alone and the
pick cell contains it together with the lift waypoint. Instance of `exists_commanded_of_run`,
whose hypothesis `busy = true` holds here. Not from MLS. -/
theorem busyState_commanded :
    ∃ w, (∀ u, u ∈ busyState.commanded ↔ u = w) ∧
      linked params.cells busyState.current w = true :=
  exists_commanded_of_run busyState_spec.1 busyState_spec.2.1

/-- The protective stop on a faulted reachable state: the state is idle. Instance of
`busy_eq_false_of_run`, whose hypothesis `faulted = true` holds here. Not from MLS. -/
theorem faultState_idle : faultState.busy = false :=
  busy_eq_false_of_run run_faultRun.1 run_faultRun.2.1

/-- The permanence of the protective stop on a faulted reachable design state: after a request,
the supervisor is still faulted, idle and without a command. Instance of
`CellSupervisor.ReachableState.faulted_step` with the step `request`. Not from MLS. -/
theorem faultState_request_step :
    let s := faultState.abstract
    let s' : CellSupervisor.State Waypoint := { s with requested := insert liftPick s.requested }
    s'.faulted = true ∧ s'.busy = false ∧ s'.commanded = ∅ :=
  (reachableState_of_run run_faultRun.1).faulted_step
    (CellSupervisor.Step.request faultState.abstract liftPick) run_faultRun.2.1

end Instances

end RoboLean.Cell.Supervisor
