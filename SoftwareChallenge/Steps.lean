import SoftwareChallenge.Lint

namespace SoftwareChallenge

def runStep (args : List String) : IO UInt32 := do
  try match args with
    | ["statement", plan] => statementStep (← Plan.load plan)
    | ["lint", plan] => lintStep (← Plan.load plan)
    | _ => usage
  catch error =>
    IO.eprintln s!"{args}: the step stopped on `{error}`, so it judged nothing. Fix what it reports, then run \
      `lake build` and `lake lint`"
    return 3
where
  usage : IO UInt32 := do
    IO.eprintln "usage: `lean --run SoftwareChallengeRun.lean (statement | lint) <plan.json>`, as the lakefile of \
      software_challenge runs it from `lake build` and `lake lint`"
    return 3

end SoftwareChallenge
