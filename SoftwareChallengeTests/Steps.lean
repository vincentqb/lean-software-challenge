module

meta import SoftwareChallenge.Steps.Schedule
meta import SoftwareChallenge.Steps.Replay

meta section

namespace SoftwareChallengeTests.Steps

open Lean SoftwareChallenge.Steps

def overlapping (jobs : Nat) : IO Bool := do
  let running ← IO.mkRef 0
  let overlapped ← IO.mkRef false
  discard <| schedule jobs #[0, 1] fun (_ : Nat) => do
    running.modify (· + 1)
    let deadline := (← IO.monoMsNow) + 500
    repeat
      if (← running.get) ≥ 2 then
        overlapped.set true
        break
      if (← IO.monoMsNow) > deadline then break
      IO.sleep 10
    running.modify (· - 1)
  overlapped.get

run_cmd Elab.Command.liftCoreM do
  unless ← overlapping 2 do throwError "with 2 jobs, schedule did not start a second task before the first finished"
  if ← overlapping 1 then throwError "with 1 job, schedule started a second task before the first finished"
  let results ← schedule 3 #[3, 1, 2] fun (n : Nat) => pure (n * 10)
  unless results.map (·.1) == #[30, 10, 20] do throwError "schedule did not keep each result at its task's index"

#guard Replay.lineOf "namespace A\ntheorem fold_idempotent (e : Expr) :\n" `A.fold_idempotent ==
  some " (Challenge.lean:2)"

#guard Replay.lineOf "theorem other : True" `A.fold_idempotent == none

#guard Replay.lineFor `A.b { exitCode := 0, stdout := "", stderr := "" } 1234 == "A.b  1.2 s"

#guard Replay.lineFor `A.b { exitCode := 1, stdout := "Challenge and solution theorem statement do not match", stderr := "" }
  0 == "A.b  0.0 s  (rejected)"

#guard Replay.lineFor `A.b { exitCode := 1, stdout := "bwrap: Can't bind mount", stderr := "" } 0 ==
  "A.b  0.0 s  (could not run, exit 1)"

end SoftwareChallengeTests.Steps
