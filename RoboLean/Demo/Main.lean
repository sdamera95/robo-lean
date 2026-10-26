import RoboLean.Demo.Supervisor

/-!
# Line protocol of the executable supervisor

`main` reads one command per line on standard input and answers one line per command on standard
output, flushing after every answer:

* `params a b bound`: set the link lengths `a`, `b` (positive rationals, written `n`, `n/d` or
  `n.f`) and the age bound (a natural number), and reset the state to `State.init`;
* `request x y`, `admit x y`, `reject x y`, `finish`, `tick`, `timeout`: apply the action with
  `step`;
* `state`: report the state; `quit`: report the state and stop.

Answers are `ok <state>` (the state as `State.render` writes it), `blocked <guard>` (the first
failing guard, as `Action.blocker` names it; the state is unchanged) or `error <reason>`. Blank
lines are ignored and the program stops at the end of its input. Because `params` resets the
state, every state reported after `params` is `run p State.init acts` for the parameters `p` and
the accepted actions `acts` since then, the case covered by `RoboLean.Demo.reachableState_of_run`.
That theorem concerns the Lean definitions; the compiler, the interpreter and the operating
system that execute them are trusted, not verified. A design model, not from MLS.
-/

namespace RoboLean.Demo

/-- Parse the arguments of `params a b bound`: positive rational link lengths and a natural
age bound. -/
def parseParams : List String → Except String Params
  | [a, b, bound] =>
    match parseRat? a, parseRat? b, parseNat? bound with
    | some a, some b, some bound =>
      if 0 < a ∧ 0 < b then .ok { a := a, b := b, bound := bound }
      else .error "link lengths must be positive"
    | _, _, _ => .error "bad params"
  | _ => .error "usage: params a b bound"

end RoboLean.Demo

open RoboLean.Demo in
/-- Run the line protocol on standard input and output. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let reply (msg : String) : IO Unit := do
    stdout.putStrLn msg
    stdout.flush
  let mut params : Option Params := none
  let mut s := State.init
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
        s := State.init
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
