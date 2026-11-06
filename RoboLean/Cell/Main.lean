import RoboLean.Cell.Policy

/-!
# Line protocol of the executable cell supervisor and its policy

`main` reads one command per line on standard input and answers one line per command on standard
output, flushing after every answer. All angles are in degrees, each a rational written `n`,
`n/d` or `n.f` with an optional leading `-`:

* `params bound h0 h1 h2 [lo0 lo1 lo2 hi0 hi1 hi2]...`: set the age bound (a natural number), the
  home waypoint `(h0, h1, h2)` and the cells, six numbers each (lower corner, upper corner), and
  reset the state to `State.init` at the home waypoint; the per-action commands are enabled;
* `request a b c`, `admit a b c`, `reject a b c`, `finish`, `tick`, `timeout`: apply the action
  with `step` (per-action commands, available between `params` and `policy`);
* `policy h T posTol velTol cpr`: after `params`, set the policy's period `h` and move duration
  `T` (seconds), its arrival tolerances (degrees, radians per second) and the encoder resolution
  (counts per revolution), reset the state to `Policy.State.init`, and switch to the boundary
  protocol: from then until the next `params` only `boundary`, `state` and `quit` are accepted;
* `boundary k c0 c1 c2 v0 v1 v2 [a b c]...`: the period boundary `k` (it must be the number of
  boundaries answered since `policy`), the sample (three encoder counts, three joint speeds in
  radians per second, each a rational) and the requests that arrived since the last boundary
  (three angles each); the program decides with `Policy.boundary` and applies every action with
  `step`;
* `state`: report the supervisor's state; `quit`: report it and stop.

Answers are `ok <state>` (the supervisor's state as `State.render` writes it) for the per-action
commands, `params`, `state` and `quit`; `ok <policy state>` for `policy`; `ok acts=<actions>
<policy state>` for `boundary`, the actions as `Policy.renderActions` and the state as
`Policy.State.render` write them; `blocked <guard>` (the first failing guard, as `Action.blocker`
names it; the state is unchanged) for a per-action command; `error <reason>` otherwise, with the
state unchanged. Blank lines are ignored and the program stops at the end of its input.

Because `params` resets the state, every state reported after `params` and before `policy` is
`run p (State.init p.home) acts` for the parameters `p` and the accepted actions `acts` since
then. Because `policy` resets the state and only `boundary` changes it afterwards, the states
reported by the answers to `boundary 0`, `boundary 1`, … are `st 1`, `st 2`, … and the actions
reported are `acts 0`, `acts 1`, … of `Policy.IsProgramRun cfg reqs smp st acts` for the
configuration `cfg` and the requests and samples sent. Those statements concern the Lean
definitions; the compiler, the interpreter and the operating system that execute them are
trusted, not verified. A design model, not from MLS.
-/

namespace RoboLean.Cell.Supervisor

/-- Parse the cells of a `params` line: groups of six rationals, the lower and the upper corner
of a box in degrees, each corner at most the other coordinate by coordinate. A design
convention, not from MLS. -/
def parseCells : List String → Except String (List Box)
  | [] => .ok []
  | a₀ :: a₁ :: a₂ :: b₀ :: b₁ :: b₂ :: rest =>
    match parseWaypoint? a₀ a₁ a₂, parseWaypoint? b₀ b₁ b₂ with
    | some lo, some hi =>
      if lo.1 ≤ hi.1 ∧ lo.2.1 ≤ hi.2.1 ∧ lo.2.2 ≤ hi.2.2 then
        (parseCells rest).map ({ lo := lo, hi := hi } :: ·)
      else .error "empty cell"
    | _, _ => .error "bad params"
  | _ => .error "bad params"

/-- Parse the arguments of `params bound h0 h1 h2 [lo0 lo1 lo2 hi0 hi1 hi2]...`: a natural age
bound, the home waypoint and the cells. A design convention, not from MLS. -/
def parseParams : List String → Except String Params
  | bound :: h₀ :: h₁ :: h₂ :: cells =>
    match RoboLean.Demo.parseNat? bound, parseWaypoint? h₀ h₁ h₂ with
    | some bound, some home =>
      (parseCells cells).map fun cs => { cells := cs, home := home, bound := bound }
    | _, _ => .error "bad params"
  | _ => .error "usage: params bound h0 h1 h2 [lo0 lo1 lo2 hi0 hi1 hi2]..."

end RoboLean.Cell.Supervisor

open RoboLean.Cell.Supervisor in
/-- Run the line protocol of the cell supervisor and its policy on standard input and output.
A design convention, not from MLS. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let reply (msg : String) : IO Unit := do
    stdout.putStrLn msg
    stdout.flush
  let mut params : Option Params := none
  let mut cfg : Option RoboLean.Cell.Policy.Config := none
  let mut st : RoboLean.Cell.Policy.State :=
    { sup := State.init (0, 0, 0), src := (0, 0, 0), goal := (0, 0, 0), start := 0, pending := [] }
  let mut next : Nat := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let words := (line.trimAscii.toString.splitOn " ").filter (· ≠ "")
    match words with
    | [] => continue
    | ["quit"] =>
      reply ("ok " ++ st.sup.render)
      break
    | ["state"] => reply ("ok " ++ st.sup.render)
    | "params" :: args =>
      match parseParams args with
      | .ok p =>
        params := some p
        cfg := none
        st := { sup := State.init p.home, src := p.home, goal := p.home, start := 0, pending := [] }
        next := 0
        reply ("ok " ++ st.sup.render)
      | .error e => reply ("error " ++ e)
    | "policy" :: args =>
      match params with
      | none => reply "error no params"
      | some p =>
        match RoboLean.Cell.Policy.parseConfig p args with
        | .ok c =>
          cfg := some c
          st := RoboLean.Cell.Policy.State.init c
          next := 0
          reply ("ok " ++ st.render)
        | .error e => reply ("error " ++ e)
    | "boundary" :: k :: c₀ :: c₁ :: c₂ :: v₀ :: v₁ :: v₂ :: reqs =>
      match cfg with
      | none => reply "error no policy"
      | some c =>
        match RoboLean.Demo.parseNat? k, RoboLean.Cell.Policy.parseSample? c₀ c₁ c₂ v₀ v₁ v₂,
            RoboLean.Cell.Policy.parseWaypoints reqs with
        | some k, some smp, some ws =>
          if k ≠ next then reply ("error expected boundary " ++ toString next)
          else
            match RoboLean.Cell.Policy.boundary c k ws smp st with
            | some (acts, st') =>
              st := st'
              next := next + 1
              reply ("ok acts=" ++ RoboLean.Cell.Policy.renderActions acts ++ " " ++ st'.render)
            | none => reply "error blocked"
        | _, _, _ => reply "error bad boundary"
    | _ =>
      match params, cfg with
      | none, _ => reply "error no params"
      | some _, some _ => reply "error policy mode"
      | some p, none =>
        match Action.parse words with
        | .error e => reply ("error " ++ e)
        | .ok act =>
          match step p st.sup act with
          | some s' =>
            st := { st with sup := s' }
            reply ("ok " ++ s'.render)
          | none => reply ("blocked " ++ (act.blocker p st.sup).getD "guard")
