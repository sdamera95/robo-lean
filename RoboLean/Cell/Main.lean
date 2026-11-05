import RoboLean.Cell.Supervisor

/-!
# Line protocol of the executable cell supervisor

`main` reads one command per line on standard input and answers one line per command on standard
output, flushing after every answer. All angles are in degrees, each a rational written `n`,
`n/d` or `n.f` with an optional leading `-`:

* `params bound h0 h1 h2 [lo0 lo1 lo2 hi0 hi1 hi2]...`: set the age bound (a natural number), the
  home waypoint `(h0, h1, h2)` and the cells, six numbers each (lower corner, upper corner), and
  reset the state to `State.init` at the home waypoint;
* `request a b c`, `admit a b c`, `reject a b c`, `finish`, `tick`, `timeout`: apply the action
  with `step`;
* `state`: report the state; `quit`: report the state and stop.

Answers are `ok <state>` (the state as `State.render` writes it), `blocked <guard>` (the first
failing guard, as `Action.blocker` names it; the state is unchanged) or `error <reason>`. Blank
lines are ignored and the program stops at the end of its input. Because `params` resets the
state, every state reported after `params` is `run p (State.init p.home) acts` for the parameters
`p` and the accepted actions `acts` since then, the case covered by
`RoboLean.Cell.Supervisor.reachableState_of_run`. That theorem concerns the Lean definitions; the
compiler, the interpreter and the operating system that execute them are trusted, not verified.
A design model, not from MLS.
-/

namespace RoboLean.Cell.Supervisor

/-- Parse the cells of a `params` line: groups of six rationals, the lower and the upper corner
of a box in degrees, each corner at most the other coordinate by coordinate. Not from MLS. -/
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
bound, the home waypoint and the cells. Not from MLS. -/
def parseParams : List String → Except String Params
  | bound :: h₀ :: h₁ :: h₂ :: cells =>
    match RoboLean.Demo.parseNat? bound, parseWaypoint? h₀ h₁ h₂ with
    | some bound, some home =>
      (parseCells cells).map fun cs => { cells := cs, home := home, bound := bound }
    | _, _ => .error "bad params"
  | _ => .error "usage: params bound h0 h1 h2 [lo0 lo1 lo2 hi0 hi1 hi2]..."

end RoboLean.Cell.Supervisor

open RoboLean.Cell.Supervisor in
/-- Run the line protocol of the cell supervisor on standard input and output. Not from MLS. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let reply (msg : String) : IO Unit := do
    stdout.putStrLn msg
    stdout.flush
  let mut params : Option Params := none
  let mut s := State.init (0, 0, 0)
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let words := (line.trimAscii.toString.splitOn " ").filter (· ≠ "")
    match words with
    | [] => continue
    | ["quit"] =>
      reply ("ok " ++ s.render)
      break
    | ["state"] => reply ("ok " ++ s.render)
    | "params" :: args =>
      match parseParams args with
      | .ok p =>
        params := some p
        s := State.init p.home
        reply ("ok " ++ s.render)
      | .error e => reply ("error " ++ e)
    | _ =>
      match params with
      | none => reply "error no params"
      | some p =>
        match Action.parse words with
        | .error e => reply ("error " ++ e)
        | .ok act =>
          match step p s act with
          | some s' =>
            s := s'
            reply ("ok " ++ s.render)
          | none => reply ("blocked " ++ (act.blocker p s).getD "guard")
